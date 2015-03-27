\begin{code}
module ListProperties where

open import Function
open import Data.Empty
open import Data.Sum renaming (_⊎_ to _∨_;map to map+)
open import Data.Nat
open import Data.Product renaming (Σ to Σₓ;map to mapₓ) 
open import Data.Bool hiding (_∨_;_≟_)
open import Data.List hiding (any)
open import Data.List hiding (any)
open import Data.List.Properties
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Properties
open import Data.List.Any.Membership
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ) 

open Any.Membership-≡ renaming (_∈_ to _∈'_;_∉_ to _∉'_) 
import Function.Equality as FE
open import Function.Inverse hiding (sym;_∘_;map;id)
open Inverse

-- Auxiliary Lemmas about lists membership
c∈xs++ys→c∈xs∨c∈ys : {x : ℕ}{xs ys : List ℕ} → x ∈' xs ++ ys → (x ∈' xs) ∨ (x ∈' ys) 
c∈xs++ys→c∈xs∨c∈ys {x} {xs} {ys} = FE.Π._⟨$⟩_ (from (++↔ {A = ℕ} {P = _≡_ x} {xs = xs} {ys = ys})) 
c∈xs∨c∈ys→c∈xs++ys : {x : ℕ}{xs ys : List ℕ} → x ∈' xs ∨ x ∈' ys → x ∈' xs ++ ys 
c∈xs∨c∈ys→c∈xs++ys {x} {xs} {ys} = FE.Π._⟨$⟩_ (to (++↔ {A = ℕ} {P = _≡_ x} {xs = xs} {ys = ys})) 
c∉xs++ys→c∉xs : {c : ℕ}{xs ys : List ℕ} → c ∉' xs ++ ys → c ∉' xs 
c∉xs++ys→c∉xs {c} {xs} {ys} c∉xs++ys c∈xs = c∉xs++ys (c∈xs∨c∈ys→c∈xs++ys (inj₁ c∈xs))
c∉xs++ys→c∉ys : {c : ℕ}{xs ys : List ℕ} → c ∉' xs ++ ys → c ∉' ys 
c∉xs++ys→c∉ys {c} {xs} {ys} c∉xs++ys c∈ys = c∉xs++ys (c∈xs∨c∈ys→c∈xs++ys {c} {xs} {ys} (inj₂ c∈ys))
d∉abc∷xs→d≢a : {a b c d : ℕ}{xs : List ℕ} → d ∉' (a ∷ b ∷ c ∷ xs) → d ≢ a
d∉abc∷xs→d≢a {a} {b} {c} {.a} {xs} d∉abc∷xs refl = ⊥-elim (d∉abc∷xs (here refl))
d∉abc∷xs→d≢b : {a b c d : ℕ}{xs : List ℕ} → d ∉' (a ∷ b ∷ c ∷ xs) → d ≢ b
d∉abc∷xs→d≢b {a} {b} {c} {.b} {xs} d∉abc∷xs refl = ⊥-elim (d∉abc∷xs (there (here refl)))
d∉abc∷xs→d≢c : {a b c d : ℕ}{xs : List ℕ} → d ∉' (a ∷ b ∷ c ∷ xs) → d ≢ c
d∉abc∷xs→d≢c {a} {b} {c} {.c} {xs} d∉abc∷xs refl = ⊥-elim (d∉abc∷xs (there (there (here refl))))
d∉abc∷xs→d∉xs : {a b c d : ℕ}{xs : List ℕ} → d ∉' (a ∷ b ∷ c ∷ xs) → d ∉' xs
d∉abc∷xs→d∉xs {a} {b} {c} {d} {xs} d∉abc∷xs d∈xs = ⊥-elim (d∉abc∷xs (there (there (there d∈xs))))
b∉a∷xs→b≢a : {a b : ℕ}{xs : List ℕ} → b ∉' (a ∷ xs) → b ≢ a
b∉a∷xs→b≢a {a} {.a} {xs} a∉a∷xs refl = ⊥-elim (a∉a∷xs (here refl))
b∉a∷xs→b∉xs : {a b : ℕ}{xs : List ℕ} → b ∉' (a ∷ xs) → b ∉' xs 
b∉a∷xs→b∉xs {a} {b} {xs} b∉a∷xs b∈xs = ⊥-elim (b∉a∷xs (there b∈xs))
--
lemmaxs++[]≡xs : {A : Set}(xs : List A) → xs ++ [] ≡ xs
lemmaxs++[]≡xs []        =  refl
lemmaxs++[]≡xs (x ∷ xs)  =  cong (_∷_ x) (lemmaxs++[]≡xs xs)
-- Auxiliary functions and properties
_-_ : List ℕ → ℕ → List ℕ
xs - x = filter (λ y → not (⌊ x ≟ y ⌋)) xs
--
lemmafilter→ : (x : ℕ)(xs : List ℕ)(p : ℕ → Bool) → x ∈' filter p xs → (p x ≡ true × x ∈' xs)
lemmafilter→ x []        p ()
lemmafilter→ x (y ∷ xs)  p x∈filterpy∷xs with p y | inspect p y
...  | false   | [ py≡false ]ᵢ = mapₓ id there (lemmafilter→ x xs p x∈filterpy∷xs)
lemmafilter→ x (.x ∷ xs) p (here refl)         
     | true | [ px≡true ]ᵢ = px≡true , here refl
lemmafilter→ x (y ∷ xs) p (there x∈filterpxs)  
     | true | [ py≡true ]ᵢ = mapₓ id there (lemmafilter→ x xs p x∈filterpxs)
\end{code}
