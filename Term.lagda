\begin{code}
module Term where

open import Atom
open import ListProperties
open import Chi
open import NaturalProperties

open import Data.Bool hiding (_∨_;_≟_)
open import Data.Product renaming (map to mapₓ)
open import Data.Sum renaming (_⊎_ to _∨_;map to map+)
open import Data.Empty
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Data.List
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Properties
open import Data.List.Any.Membership
open Any.Membership-≡ renaming (_∈_ to _∈'_;_∉_ to _∉'_) 
open import Data.Nat as Nat hiding (_⊔_;_*_)
open import Data.Nat.Properties
open DecTotalOrder Nat.decTotalOrder using () renaming (refl to ≤-refl)
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _◽; _≡⟨_⟩_ to _≤⟨_⟩'_)

infix  9 _·_ 
infix  5 （_∙_）_ 
infix  3 _∈_ _∉_ _#_ _*_
\end{code}

%<*term>
\begin{code}
data Λ : Set where
  v    : Atom → Λ 
  _·_  : Λ → Λ → Λ 
  ƛ    : Atom → Λ → Λ 
\end{code}
%</term>

\begin{code}
∣_∣ : Λ → ℕ
∣ v a ∣    = 1
∣ M · N ∣  = ∣ M ∣ + ∣ N ∣
∣ ƛ a M ∣  =  1 + ∣ M ∣
--
lemma∣M∣>0 : {M : Λ} → ∣ M ∣ > zero
lemma∣M∣>0 {v x}    = s≤s z≤n
lemma∣M∣>0 {M · N}  
  = start
      suc zero
    ≤⟨ lemma∣M∣>0 {M} ⟩
      ∣ M ∣
    ≤⟨ m≤m+n ∣ M ∣ ∣ N ∣ ⟩
      ∣ M ∣ + ∣ N ∣
    ≤⟨ ≤-refl ⟩
      ∣ M · N ∣
    ◽
--
lemma∣M∣>0 {ƛ a M}  
  = start
      suc zero 
    ≤⟨ s≤s z≤n ⟩
      suc (suc zero)
    ≤⟨ s≤s (lemma∣M∣>0 {M}) ⟩
      1 + ∣ M ∣
    ≤⟨ ≤-refl ⟩
      ∣ ƛ a M ∣
    ◽
--
lemma∣va∣ : ∀ {N} → ∣ N ∣ ≤′ 1 → Σ Atom  (λ a → N  ≡ v a)
lemma∣va∣ {v a}    |N|≤1    = a , refl
lemma∣va∣ {M · N}  |MN|≤1   = ⊥-elim (>1→¬≤1 {∣ M ∣ + ∣ N ∣} (lemmam>0∧n>0→m+n>1 {∣ M ∣} {∣ N ∣} (lemma∣M∣>0 {M}) (lemma∣M∣>0  {N})) (≤′⇒≤ |MN|≤1)) 
lemma∣va∣ {ƛ a M}  |ƛaM|≤1  = ⊥-elim (>1→¬≤1 {1 + ∣ M ∣} (lemmam>0∧n>0→m+n>1 {1} {∣ M ∣} (s≤s z≤n) (lemma∣M∣>0 {M})) (≤′⇒≤ |ƛaM|≤1)) 
--
data _∈_ (a : Atom) : Λ → Set where
  ∈v   : a ∈ v a 
  ∈·r  : {M N  : Λ}            → a ∈ N  → a ∈ M · N
  ∈·l  : {M N  : Λ} → a ∈ M    → a ∈ M · N
  ∈ƛr  : {b : Atom}{M    : Λ}  → a ∈ M  → a ∈ ƛ b M
  ∈ƛl  : {M    : Λ}            → a ∈ ƛ a M
--
data _∉_ (a : Atom) : Λ → Set where
  ∉v   : {b : Atom}            → b ≢ a          → a ∉ v b 
  ∉·   : {M N  : Λ}            → a ∉ M → a ∉ N  → a ∉ M · N
  ∉ƛ   : {b : Atom}{M    : Λ}  → b ≢ a → a ∉ M  → a ∉ ƛ b M
\end{code}

%<*fresh>
\begin{code}
data _#_ (a : Atom) :  Λ → Set where
  #v   : {b : Atom}         → b ≢ a          → a # v b
  #·   : {M N : Λ }         → a # M → a # N  → a # M · N
  #ƛ≡  : {M : Λ}                             → a # ƛ a M
  #ƛ   : {b : Atom}{M : Λ}  → a # M          → a # ƛ b M
\end{code}
%</fresh>

%<*free>
\begin{code}
data _*_ : Atom → Λ → Set where
  *v   :  {x : Atom}                           → x * v x
  *·l  :  {x : Atom}{M N : Λ} → x * M          → x * (M · N)
  *·r  :  {x : Atom}{M N : Λ} → x * N          → x * (M · N)
  *ƛ   :  {x y : Atom}{M : Λ} → x * M → y ≢ x  → x * (ƛ y M)
\end{code}
%</free>

\begin{code}
lemma#λ : {a b : Atom}{M : Λ} → a ≢ b → a # ƛ b M → a # M
lemma#λ b≢b #ƛ≡       = ⊥-elim (b≢b refl)
lemma#λ a≢b (#ƛ a#M)  = a#M
--
lemma∉→¬∈ : {a : Atom}{M : Λ} → a ∉ M → ¬ (a ∈ M)
lemma∉→¬∈ (∉v a≢a) ∈v               = ⊥-elim (a≢a refl)
lemma∉→¬∈ (∉· a∉M a∉N)  (∈·r a∈N)  = ⊥-elim ((lemma∉→¬∈ a∉N) a∈N)
lemma∉→¬∈ (∉· a∉M a∉N)  (∈·l a∈M)  = ⊥-elim ((lemma∉→¬∈ a∉M) a∈M)
lemma∉→¬∈ (∉ƛ b≢a a∉M)  (∈ƛr a∈M)  = ⊥-elim ((lemma∉→¬∈ a∉M) a∈M)
lemma∉→¬∈ (∉ƛ a≢a a∉M)  ∈ƛl        = ⊥-elim (a≢a refl)
--
lemma∉→# : {a : Atom}{M : Λ} → a ∉ M → a # M
lemma∉→# (∉v b≢a)       = #v b≢a
lemma∉→# (∉· a∉M a∉N)  = #· (lemma∉→# a∉M) (lemma∉→# a∉N)
lemma∉→# (∉ƛ b≢a a∉M)   = #ƛ (lemma∉→# a∉M)
--
lemma-free→∈ : {x : Atom}{M : Λ} → x * M → x ∈ M
lemma-free→∈ *v            = ∈v
lemma-free→∈ (*·l x*M)     = ∈·l (lemma-free→∈ x*M)
lemma-free→∈ (*·r x*M)     = ∈·r (lemma-free→∈ x*M)
lemma-free→∈ (*ƛ x*M y≢x)  = ∈ƛr (lemma-free→∈ x*M)
--
ocurr : Λ → List Atom
ocurr (v a)    = [ a ]
ocurr (M · N)  = ocurr M ++ ocurr N
ocurr (ƛ x M)  = x ∷ ocurr M
--
lemmaocurr : {a : Atom}{M : Λ} → a ∉' ocurr M → a ∉ M
lemmaocurr {a} {v b}    a∉[b]             
  with b ≟ₐ a 
... | no b≢a    = ∉v b≢a
lemmaocurr {a} {v .a}    a∉[a]             
    | yes refl  = ⊥-elim (a∉[a] (here refl))
lemmaocurr {a} {M · N}  a∉ocurrM++ocurrN  
  = ∉·  (lemmaocurr (c∉xs++ys→c∉xs a∉ocurrM++ocurrN))
        (lemmaocurr (c∉xs++ys→c∉ys {a} {ocurr M} a∉ocurrM++ocurrN))
lemmaocurr {a} {ƛ b M}  a∉b∷ocurrM
  with b ≟ₐ a 
... | no b≢a    = ∉ƛ b≢a (lemmaocurr (a∉b∷ocurrM ∘ there)) 
lemmaocurr {a} {ƛ .a M}  a∉b∷ocurrM
    | yes refl  = ⊥-elim (a∉b∷ocurrM (here refl))
--
_#?_ : Decidable _#_
x #? (v y) with y ≟ₐ x
... | yes y≡x = no (λ {(#v y≢x) → y≢x y≡x})
... | no  y≢x = yes (#v y≢x)
x #? (M · N) with x #? M | x #? N 
... | yes x#M | yes  x#N = yes (#· x#M x#N)
... | yes x#M | no  ¬x#N = no (λ {(#· _ x#N) → ¬x#N x#N})
... | no ¬x#M | yes  x#N = no (λ {(#· x#M _)   → ¬x#M x#M})
... | no ¬x#M | no  ¬x#N = no (λ {(#· x#M _)   → ¬x#M x#M})
x #? (ƛ y M) with y | x ≟ₐ y 
... | .x | yes refl = yes #ƛ≡
... | _  | no  x≢y with x #? M
...                | yes  x#M = yes (#ƛ x#M) 
x #? (ƛ y M) 
    | w  | no  x≢w | no  ¬x#M = no (aux x≢w ¬x#M)
  where aux : {x w : Atom} → x ≢ w → ¬ (x # M) →  x # ƛ w M → ⊥
        aux x≢w ¬x#ƛwM #ƛ≡         =  ⊥-elim (x≢w refl)
        aux x≢w ¬x#ƛwM (#ƛ x#ƛwM)  =  ⊥-elim (¬x#ƛwM x#ƛwM)
--
lemma¬#→free : {x : Atom}{M : Λ} → ¬ (x # M) → x * M
lemma¬#→free {x} {v y} ¬x#M with y ≟ₐ x
... | no  y≢x   = ⊥-elim (¬x#M (#v y≢x))
lemma¬#→free {x} {v .x} ¬x#M 
    | yes refl  = *v
lemma¬#→free {x} {M · N} ¬x#MN with x #? M | x #? N 
... | yes x#M | yes x#N = ⊥-elim (¬x#MN (#· x#M x#N))
... | yes x#M | no ¬x#N = *·r (lemma¬#→free ¬x#N)
... | no ¬x#M | yes x#N = *·l (lemma¬#→free ¬x#M)
... | no ¬x#M | no ¬x#N = *·r (lemma¬#→free ¬x#N)
lemma¬#→free {x} {ƛ y M} ¬x#λxM with y ≟ₐ x
... | no  y≢x with x #? M
... | yes x#M = ⊥-elim (¬x#λxM (#ƛ x#M))
... | no ¬x#M = *ƛ (lemma¬#→free ¬x#M) y≢x
lemma¬#→free {x} {ƛ .x M} ¬x#λxM 
    | yes refl = ⊥-elim (¬x#λxM #ƛ≡)
--
lemma-free→¬# : {x : Atom}{M : Λ} → x * M →  ¬ (x # M)
lemma-free→¬# {x} {v .x} *v            (#v x≢x) 
  = ⊥-elim (x≢x refl)
lemma-free→¬# {x} {M · N} (*·l xfreeM) (#· x#M x#N) 
  = ⊥-elim ((lemma-free→¬# xfreeM) x#M)
lemma-free→¬# {x} {M · N} (*·r xfreeN) (#· x#M x#N) 
  = ⊥-elim ((lemma-free→¬# xfreeN) x#N)
lemma-free→¬# {x} {ƛ .x M} (*ƛ xfreeM x≢x) #ƛ≡
  = ⊥-elim (x≢x refl)
lemma-free→¬# {x} {ƛ y M} (*ƛ xfreeM y≢x) (#ƛ x#M)  
  = ⊥-elim ((lemma-free→¬# xfreeM) x#M)
\end{code}

Term swap

%<*swap>
\begin{code}
（_∙_）_ : Atom → Atom → Λ → Λ
（ a ∙ b ） v c    = v (（ a ∙ b ）ₐ c)
（ a ∙ b ） M · N  = (（ a ∙ b ） M) ·  (（ a ∙ b ） N)  
（ a ∙ b ） ƛ c M  = ƛ (（ a ∙ b ）ₐ c) (（ a ∙ b ） M)
\end{code}
%</swap>

\begin{code} 
lemma∙cancel∉ : {a b : Atom}{M : Λ} → a ∉ M → b ∉ M → （ a ∙ b ） M ≡ M 
lemma∙cancel∉ {a} {b} {v c}    (∉v c≢a)      (∉v c≢b)     = cong v (lemma∙ₐc≢a∧c≢b c≢a c≢b)
lemma∙cancel∉ {a} {b} {M · N}  (∉· a∉M a∉N)  (∉· b∉M b∉N) = cong₂ _·_ (lemma∙cancel∉ a∉M b∉M) (lemma∙cancel∉ a∉N b∉N)
lemma∙cancel∉ {a} {b} {ƛ c M}  (∉ƛ c≢a a∉M)  (∉ƛ c≢b b∉M) = cong₂ ƛ (lemma∙ₐc≢a∧c≢b c≢a c≢b) (lemma∙cancel∉ a∉M b∉M)
--
lemma∙∣∣ : {M : Λ}{a b : Atom} → ∣ （ a ∙ b ） M ∣ ≡ ∣ M ∣ 
lemma∙∣∣ {v c}    = refl
lemma∙∣∣ {M · N}  = cong₂ _+_ (lemma∙∣∣ {M}) (lemma∙∣∣ {N})
lemma∙∣∣ {ƛ c M}  = cong suc (lemma∙∣∣ {M})
--
lemma∙∣∣≤ : {M : Λ}{a b : Atom} → ∣ （ a ∙ b ） M ∣ ≤′ ∣ M ∣ 
lemma∙∣∣≤ {M} {a} {b} rewrite lemma∙∣∣ {M} {a} {b} = ≤′-refl
--
lemma∙∙∣∣≤ :  ∀ {a} {b} {c} {M} → ∣ （ b ∙ c ） （ a ∙ b ） M ∣ ≤′ ∣ M ∣
lemma∙∙∣∣≤ {a} {b} {c} {M} rewrite lemma∙∣∣ {（ a ∙ b ） M} {b} {c} | lemma∙∣∣ {M} {a} {b} = ≤′-refl
--
lemma（aa）M≡M : {a : Atom}{M : Λ} → （ a ∙ a ） M ≡ M 
lemma（aa）M≡M {a} {v b}    = cong   v    lemma（aa）b≡b
lemma（aa）M≡M {a} {M · N}  = cong₂  _·_  lemma（aa）M≡M  lemma（aa）M≡M
lemma（aa）M≡M {a} {ƛ b M}  = cong₂  ƛ    lemma（aa）b≡b  lemma（aa）M≡M
--
lemma（ab）（ab）M≡M : {a b : Atom}{M : Λ} → （ a ∙ b ） （ a ∙ b ） M ≡ M 
lemma（ab）（ab）M≡M {a} {b} {v c}    = cong   v    lemma（ab）（ab）c≡c
lemma（ab）（ab）M≡M {a} {b} {M · N}  = cong₂  _·_  lemma（ab）（ab）M≡M  lemma（ab）（ab）M≡M
lemma（ab）（ab）M≡M {a} {b} {ƛ c M}  = cong₂  ƛ    lemma（ab）（ab）c≡c  lemma（ab）（ab）M≡M
--
lemma∙comm : {a b : Atom}{M : Λ} → （ a ∙ b ） M ≡ （ b ∙ a ） M 
lemma∙comm {a} {b} {v c}    = cong   v    (lemma∙ₐcomm {a} {b} {c})
lemma∙comm {a} {b} {M · N}  = cong₂  _·_  lemma∙comm                 lemma∙comm
lemma∙comm {a} {b} {ƛ c M}  = cong₂  ƛ    (lemma∙ₐcomm {a} {b} {c})  lemma∙comm
--
lemma∙distributive :  {a b c d : Atom}{M : Λ} →
                      （ a ∙ b ） （ c ∙ d ） M ≡ （ （ a ∙ b ）ₐ c ∙ （ a ∙ b ）ₐ d ） （ a ∙ b ） M
lemma∙distributive {a} {b} {c} {d} {v e}    
  = cong   v    (lemma∙ₐdistributive a b c d e)
lemma∙distributive {a} {b} {c} {d} {M · N}  
  = cong₂  _·_  (lemma∙distributive {a} {b} {c} {d})  lemma∙distributive
lemma∙distributive {a} {b} {c} {d} {ƛ e M}  
  = cong₂  ƛ    (lemma∙ₐdistributive a b c d e)       lemma∙distributive
--
-- lemma∙distributive2 :  {a b c d : Atom}{M : Λ} →
--                        （ a ∙ b ） （ c ∙ d ） M ≡ （ c ∙ d ） （ （ c ∙ d ）ₐ a ∙ （ c ∙ d ）ₐ b ） M
--
lemma∙cancel : {a b c : Atom}{M : Λ} → b ∉ M → c ∉ M → （ c ∙ b ） （ a ∙ c ） M ≡ （ a ∙ b ） M 
lemma∙cancel {a} {b} {c} {v d}    (∉v d≢b)      (∉v d≢c)       = cong v     (lemma∙ₐcancel d≢b d≢c)
lemma∙cancel {a} {b} {c} {M · N}  (∉· b∉M b∉N)  (∉· c∉M c∉N)   = cong₂ _·_  (lemma∙cancel b∉M c∉M)   (lemma∙cancel b∉N c∉N)
lemma∙cancel {a} {b} {c} {ƛ d M}  (∉ƛ d≢b b∉M)  (∉ƛ d≢c c∉M)   = cong₂ ƛ    (lemma∙ₐcancel d≢b d≢c)  (lemma∙cancel b∉M c∉M)
--
fv : Λ → List Atom
fv (v a)     = [ a ]
fv (M · N)   = fv M ++ fv N
fv (ƛ a M)   = fv M - a
--
lemmafvfree→ : (x : Atom)(M : Λ) → x ∈' fv M → x * M
lemmafvfree→ x (v y)    (here x≡y) with y ≟ x 
... | no   y≢x = ⊥-elim (y≢x (sym x≡y)) 
lemmafvfree→ x (v .x)    (here x≡x) 
    | yes  refl = *v
lemmafvfree→ x (v y) (there ()) 
lemmafvfree→ x (M · N)  x∈fvMN with c∈xs++ys→c∈xs∨c∈ys  x∈fvMN 
... | inj₁ x∈fvM = *·l (lemmafvfree→ x M x∈fvM)
... | inj₂ x∈fvN = *·r (lemmafvfree→ x N x∈fvN)
lemmafvfree→ x (ƛ y M)  x∈fvM-y with y ≟ x | lemmafilter→ x (fv M) (λ z → not (⌊ y ≟ z ⌋)) x∈fvM-y
... | no y≢x   | _ , x∈fvM = *ƛ (lemmafvfree→ x M x∈fvM) y≢x 
lemmafvfree→ x (ƛ .x M)  x∈fvM-y 
    | yes refl | () , _  
-- 
lemmafvfree← : (x : Atom)(M : Λ) → x * M → x ∈' fv M
lemmafvfree← x (v .x)    *v             
  = here refl
lemmafvfree← x .(M · N)  (*·l {.x} {M} {N} xfreeM)     
  = c∈xs∨c∈ys→c∈xs++ys (inj₁ (lemmafvfree← x M xfreeM))
lemmafvfree← x .(M · N)  (*·r {.x} {M} {N} xfreeN)     
  = c∈xs∨c∈ys→c∈xs++ys {x} {fv M} (inj₂ (lemmafvfree← x N xfreeN))
lemmafvfree← x .(ƛ y M)  (*ƛ {.x} {y} {M} xfreeM y≢x)  
  = filter-∈ (λ z → not (⌊ y ≟ z ⌋)) (fv M) {x} (lemmafvfree← x M xfreeM) px≡true 
  where 
  px≡true : not ⌊ y ≟ x ⌋ ≡ true
  px≡true with y ≟ x
  ... | yes y≡x = ⊥-elim (y≢x y≡x)
  ... | no  _   = refl
-- Chi encapsulation
χ : List Atom → Λ → Atom
χ xs M = χ' (xs ++ fv M) 
--
χ'∉ : (xs : List Atom) → χ' xs ∉' xs
χ'∉ = lemmaχaux∉
--
χ∉ : (xs : List Atom)(M : Λ) → χ xs M ∉' xs
χ∉ xs M = c∉xs++ys→c∉xs  (χ'∉ (xs ++ fv M))
--
χ# : (xs : List Atom)(M : Λ) → χ xs M # M
χ# xs M with (χ xs M) #? M
... | yes χ#M = χ#M
... | no ¬χ#M = ⊥-elim ((c∉xs++ys→c∉ys {χ xs M} {xs} (lemmaχaux∉ (xs ++ fv M))) (lemmafvfree← (χ xs M) M (lemma¬#→free ¬χ#M))) 
--
lemma*swap→ : {a b c : Atom}{M : Λ} → a ≢ c → a ≢ b → a * M → a * （ b ∙ c ） M
lemma*swap→ {a} {b} {c} {v .a} a≢c a≢b *v with （ b ∙ c ）ₐ a | lemma∙ₐ b c a
... | _   | inj₁ (a≡b , _)              = ⊥-elim (a≢b a≡b)
... | _   | inj₂ (inj₁ (a≡c , _))       = ⊥-elim (a≢c a≡c)
... | .a  | inj₂ (inj₂ (_ , _ , refl))  = *v
lemma*swap→ a≢c a≢b (*·l a*M) = *·l (lemma*swap→ a≢c a≢b a*M)
lemma*swap→ a≢c a≢b (*·r a*M) = *·r (lemma*swap→ a≢c a≢b a*M)
lemma*swap→ {a} {b} {c} {ƛ d M} a≢c a≢b (*ƛ a*M d≢a) 
  with （ b ∙ c ）ₐ d | lemma∙ₐ b c d
... | .c  | inj₁ (d≡b , refl)               = *ƛ (lemma*swap→ a≢c a≢b a*M) (sym≢ a≢c)
... | .b  | inj₂ (inj₁ (d≡c , _   , refl))        = *ƛ (lemma*swap→ a≢c a≢b a*M) (sym≢ a≢b)
... | .d  | inj₂ (inj₂ (d≢b , d≢c , refl))  = *ƛ (lemma*swap→ a≢c a≢b a*M) d≢a
--
lemma*swap← : {a b c : Atom}{M : Λ} → a * （ b ∙ c ） M → (a ≢ b × a ≢ c × a * M) ∨ (a ≡ b × c * M) ∨ (a ≡ c × b * M)
lemma*swap← {a} {b} {c} {v d}   a*（bc）d with （ b ∙ c ）ₐ d | lemma∙ₐ b c d 
lemma*swap← {a} {b} {.a} {v .b} *v | .a | inj₁ (refl , refl)              = inj₂ (inj₂ (refl , *v))
lemma*swap← {a} {.a} {c} {v .c} *v | .a | inj₂ (inj₁ (refl , _  , refl))  = inj₂ (inj₁ (refl , *v))
lemma*swap← {a} {b} {c} {v .a}  *v | .a | inj₂ (inj₂ (a≢b , a≢c , refl))  = inj₁ (a≢b , a≢c  , *v) 
lemma*swap← {a} {b} {c} {M · N}   (*·l a*（bc）M)  = map+ (mapₓ id (mapₓ id *·l)) (map+ (mapₓ id *·l) (mapₓ id *·l)) (lemma*swap← a*（bc）M)
lemma*swap← {a} {b} {c} {M · N}   (*·r a*（bc）N)  = map+ (mapₓ id (mapₓ id *·r)) (map+ (mapₓ id *·r) (mapₓ id *·r)) (lemma*swap← a*（bc）N)
lemma*swap← {a} {b} {c} {ƛ d M}   (*ƛ a*（bc）M （bc）d≢a) with （ b ∙ c ）ₐ d | lemma∙ₐ b c d
lemma*swap← {a} {b} {c} {ƛ .b M}  (*ƛ a*（bc）M c≢a)  | .c | inj₁ (refl , refl) with lemma*swap← a*（bc）M 
... | inj₁ (a≢b , a≢c , a*M)    =  inj₁ (a≢b , a≢c , *ƛ a*M (sym≢ a≢b))
... | inj₂ (inj₂ (a≡c , b*M))   = ⊥-elim (c≢a (sym a≡c))
lemma*swap← {a} {.a} {c} {ƛ .a M} (*ƛ a*（bc）M c≢a)  | .c | inj₁ (refl , refl) 
    | inj₂ (inj₁ (refl , c*M))  =  inj₂ (inj₁ (refl , *ƛ c*M (sym≢ c≢a)))
lemma*swap← {a} {b} {c} {ƛ .c M} (*ƛ a*（bc）M b≢a)  | .b | inj₂ (inj₁ (refl , _ , refl)) with lemma*swap← a*（bc）M 
... | inj₁ (a≢b , a≢c , a*M)    = inj₁ (a≢b , a≢c , *ƛ a*M (sym≢ a≢c))
... | inj₂ (inj₁ (a≡b , c*M))   =  ⊥-elim (b≢a (sym a≡b))
lemma*swap← {a} {b} {.a} {ƛ .a M} (*ƛ a*（ba）M b≢a)  | .a | inj₂ (inj₁ (refl , _ , refl))
    | inj₂ (inj₂ (refl , b*M))  = inj₂ (inj₂ (refl , *ƛ b*M (sym≢ b≢a)))
lemma*swap← {a} {b} {c} {ƛ d M} (*ƛ a*（bc）M d≢a)   | .d | inj₂ (inj₂ (d≢b , d≢c , refl)) 
  with lemma*swap← a*（bc）M 
... | inj₁ (a≢b , a≢c , a*M)        = inj₁ (a≢b , a≢c , *ƛ a*M d≢a)
... | inj₂ (inj₁ (a≡b , c*M))   = inj₂ (inj₁ (a≡b , *ƛ c*M d≢c))
... | inj₂ (inj₂ (a≡c , b*M))   = inj₂ (inj₂ (a≡c , *ƛ b*M d≢b))
--
lemma*swap←≢ : {a b c : Atom}{M : Λ} → a ≢ b → a ≢ c → a * （ b ∙ c ） M → a * M
lemma*swap←≢ {a} {b}  {c}   {M} a≢b a≢c a*（bc）M  with lemma*swap← {a} {b} {c} {M} a*（bc）M
lemma*swap←≢ {a} {b}  {c}   {M} a≢b a≢c a*（bc）M | inj₁ (_ , _ , a*M) = a*M
lemma*swap←≢ {a} {.a} {c}   {M} a≢a a≢c a*（bc）M | inj₂ (inj₁ (refl , _)) = ⊥-elim (a≢a refl)
lemma*swap←≢ {a} {b}  {.a}  {M} a≢b a≢a a*（bc）M | inj₂ (inj₂ (refl , _)) = ⊥-elim (a≢a refl)
\end{code}
