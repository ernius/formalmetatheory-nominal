\begin{code}
module TermRecursion where

open import Atom
open import Term
open import Alpha
open import TermAcc
open import Chi
open import ListProperties
open import TermInduction
open import Permutation

open import Data.Nat
open import Data.Nat.Properties
open import Function
open import Data.List 
open import Data.List.Any as Any hiding (map)
open Any.Membership-≡ renaming (_∈_ to _∈'_;_∉_ to _∉'_) 
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _□)
import Relation.Binary.PreorderReasoning as PreR
open PreR ≈-preorder
\end{code}

Hago ahora el principio de Iteracion con el principio de induccion de swap hecho con rec primitiva !!!

%<*termIteration>
\begin{code}
ΛIt  : (A : Set)
 → (Atom → A)
 → (A → A → A)
 → List Atom × (Atom → A → A) 
 → Λ → A
\end{code}
%</termIteration>

\begin{code}
ΛIt A hv h· (xs , hƛ) 
  = TermαIndPerm  (λ _ → A) (λ _ → id) 
                  hv (λ _ _ → h·) (xs , (λ _ b _ f → hƛ b (f [])))
\end{code}
--
-- Hacer induccion swap ????
\begin{code}
P : (A : Set) → (Atom → A) → (A → A → A) → List Atom → (Atom → A → A) → Λ → Set
P A hv h· xs hƛ M =
    ∀ π → 
    (TermPrimInd (λ M₁ → (π : List (Atom × Atom)) → A) (lemmavIndSw {λ _ → A} hv)
      (lemma·IndSw (λ _ _ → h·))
      (lemmaƛIndSw {λ _ → A}
        (lemmaαƛ (λ _ → A) (λ  _ → id) xs (λ _ b _ f → hƛ b (f []))))
      M π)
    ≡
    (TermPrimInd (λ M₁ → (π : List (Atom × Atom)) → A) (lemmavIndSw {λ _ → A} hv)
      (lemma·IndSw (λ _ _ → h·))
      (lemmaƛIndSw {λ _ → A}
        (lemmaαƛ (λ _ → A) (λ  _ → id) xs (λ _ b _ f → hƛ b (f []))))
      (π ∙ M) [])
--
aux'' : (A : Set)
  → (hv : Atom → A)
  → (h· : A → A → A)
  → (xs : List Atom)
  → (hƛ : Atom → A → A)
  → ∀ M → P A hv h· xs hƛ M
aux'' A hv h· xs hƛ 
  = TermIndPerm (P A hv h· xs hƛ) lemmav lemma· lemmaƛ  
  where
  lemmav : (a : ℕ) → P A hv h· xs hƛ (v a)
  lemmav a π rewrite lemmaπv {a} {π} = refl
  lemma· :  (M N : Λ) → P A hv h· xs hƛ M → P A hv h· xs hƛ N → P A hv h· xs hƛ (M · N)
  lemma· M N PM PN π rewrite lemmaπ· {M} {N} {π} = cong₂ h· (PM π) (PN π)
  lemmaƛ :  (M : Λ) (b : ℕ) → ((π : List (Atom × Atom)) → P A hv h· xs hƛ (π ∙ M)) 
            → P A hv h· xs hƛ (ƛ b M)
  lemmaƛ M a PMπ π rewrite lemmaπƛ {a} {M} {π} 
    = cong₂ hƛ refl (begin≡
                      TermPrimInd (λ M₁ → (π : List (Atom × Atom)) → A) (lemmavIndSw {λ _ → A} hv)
                        (lemma·IndSw (λ _ _ → h·))
                        (lemmaƛIndSw {λ _ → A}
                        (lemmaαƛ (λ _ → A) (λ  _ → id) xs (λ _ b _ f → hƛ b (f []))))
                        M ((π ∙ₐ a ,  χ xs (ƛ (π ∙ₐ a) (π ∙ M))) ∷ π)
                    ≡⟨ PMπ [] ((π ∙ₐ a ,  χ xs (ƛ (π ∙ₐ a) (π ∙ M))) ∷ π)  ⟩
                      TermPrimInd (λ M₁ → (π : List (Atom × Atom)) → A) (lemmavIndSw {λ _ → A} hv)
                        (lemma·IndSw (λ _ _ → h·))
                        (lemmaƛIndSw {λ _ → A}
                        (lemmaαƛ (λ _ → A) (λ  _ → id) xs (λ _ b _ f → hƛ b (f []))))
                        (((π ∙ₐ a ,  χ xs (ƛ (π ∙ₐ a) (π ∙ M))) ∷ π) ∙ M) []
                    ≡⟨  cong  (λ p → TermPrimInd  (λ M₁ → (π : List (Atom × Atom)) → A) (lemmavIndSw {λ _ → A} hv)
                                                   (lemma·IndSw (λ _ _ → h·))
                                                   (lemmaƛIndSw {λ _ → A}
                                                   (lemmaαƛ (λ _ → A) (λ  _ → id) xs (λ _ b _ f → hƛ b (f []))))
                                                   p [])
                               (sym (lemmaπ∙π′∙M≡π++π′∙M {[ π ∙ₐ a , χ xs (ƛ (π ∙ₐ a) (π ∙ M))]} {π} {M})) ⟩
                      TermPrimInd (λ M₁ → (π : List (Atom × Atom)) → A) (lemmavIndSw {λ _ → A} hv)
                        (lemma·IndSw (λ _ _ → h·))
                        (lemmaƛIndSw {λ _ → A}
                        (lemmaαƛ (λ _ → A) (λ  _ → id) xs (λ _ b _ f → hƛ b (f []))))
                        ([(π ∙ₐ a ,  χ xs (ƛ (π ∙ₐ a) (π ∙ M)))] ∙ π ∙ M) []
                    ≡⟨ sym (PMπ π [(π ∙ₐ a ,  χ xs (ƛ (π ∙ₐ a) (π ∙ M)))])  ⟩
                      TermPrimInd (λ M₁ → (π : List (Atom × Atom)) → A) (lemmavIndSw {λ _ → A} hv)
                        (lemma·IndSw (λ _ _ → h·))
                        (lemmaƛIndSw {λ _ → A}
                        (lemmaαƛ (λ _ → A) (λ  _ → id) xs (λ _ b _ f → hƛ b (f []))))
                        (π ∙ M) [(π ∙ₐ a ,  χ xs (ƛ (π ∙ₐ a) (π ∙ M)))]
                   □)
--
aux : (A : Set)
  → (hv : Atom → A)
  → (h· : A → A → A)
  → (xs : List Atom)
  → (hƛ : Atom → A → A)
  → ∀ π M →
    (TermPrimInd (λ M₁ → (π : List (Atom × Atom)) → A) (lemmavIndSw {λ _ → A} hv)
      (lemma·IndSw (λ _ _ → h·))
      (lemmaƛIndSw {λ _ → A}
        (lemmaαƛ (λ _ → A) (λ  _ → id) xs (λ _ b _ f → proj₂ (xs , hƛ) b (f []))))
      M
      (π ++ [])) ≡
    (TermPrimInd (λ M₁ → (π : List (Atom × Atom)) → A) (lemmavIndSw {λ _ → A} hv)
      (lemma·IndSw (λ _ _ → h·))
      (lemmaƛIndSw {λ _ → A}
        (lemmaαƛ (λ _ → A) (λ  _ → id) xs (λ _ b _ f → proj₂ (xs , hƛ) b (f []))))
      (π ∙ M)
      [])
aux A hv h· xs hƛ π M rewrite lemmaxs++[]≡xs π = aux'' A hv h· xs hƛ M π -- π M (accesibleTermsSizesƛ M) 
--
ΛItƛ  : (A : Set)
  → (hv : Atom → A)
  → (h· : A → A → A)
  → (xs : List Atom)
  → (hƛ : Atom → A → A)
  → ∀ a M 
  → ΛIt A hv h· (xs , hƛ) (ƛ a M) ≡ 
    hƛ  (χ xs (ƛ a M)) 
        (ΛIt A hv h· (xs , hƛ) ([ a , (χ xs (ƛ a M))] ∙ M))
ΛItƛ A hv h· xs hƛ a M
 = cong₂ hƛ refl (aux A hv h· xs hƛ [ a , χ xs (ƛ a M)] M)  
\end{code}

%<*iterationStrongCompatible>
\begin{code}
lemmaItαStrongCompatible : (A : Set)
  → (hv : Atom → A)
  → (h· : A → A → A)
  → (xs : List Atom)
  → (hƛ : Atom → A → A )
  → (M : Λ) → strong∼αCompatible (ΛIt A hv h· (xs , hƛ)) M 
\end{code}
%</iterationStrongCompatible>

\begin{code}
lemmaItαStrongCompatible A hv h· xs hƛ = TermIndPerm (strong∼αCompatible (ΛIt A hv h· (xs , hƛ))) lemmav lemma· lemmaƛ  
  where
  lemmav :  (a : ℕ) → strong∼αCompatible (ΛIt A hv h· (xs , hƛ)) (v a)
  lemmav a .(v a) ∼αv = refl
  lemma· :  (M N : Λ)
            → strong∼αCompatible (ΛIt A hv h· (xs , hƛ)) M 
            → strong∼αCompatible (ΛIt A hv h· (xs , hƛ)) N 
            → strong∼αCompatible (ΛIt A hv h· (xs , hƛ)) (M · N)
  lemma· M N PM PN .(M' · N') (∼α· {.M} {M'} {.N} {N'} M∼M' N∼N') 
    = cong₂ h· (PM M' M∼M') (PN N' N∼N')
  lemmaƛ :  (M : Λ) (b : ℕ) 
            → ((π : List (Atom × Atom)) → strong∼αCompatible (ΛIt A hv h· (xs , hƛ)) (π ∙ M)) 
            → strong∼αCompatible (ΛIt A hv h· (xs , hƛ)) (ƛ b M)
  lemmaƛ M a PπM .(ƛ b N) (∼αƛ {.M} {N} {.a} {b} vs fα) 
    rewrite 
       ΛItƛ A hv h· xs hƛ a M 
    |  ΛItƛ A hv h· xs hƛ b N 
    with χ xs (ƛ a M) | χ xs (ƛ b N) 
    |  χ# xs (ƛ a M) | χ# xs (ƛ b N) 
    |  χ∼α  (ƛ a M) (ƛ b N) xs (∼αƛ {M} {N} {a} {b} vs fα)  
    |  χ' (vs ++ ocurr (M · N)) | χ'∉ (vs ++ ocurr (M · N))
  ... | c | .c | c#λaM | c#λbN | refl | d | d∉vs++ocurrM·N 
    = cong₂ hƛ refl (PπM [(a , c)] (（ b ∙ c ） N) （ac）M∼α（bc）N)
    where
    d∉vs : d ∉' vs
    d∉vs = c∉xs++ys→c∉xs {d} {vs} {ocurr (M · N)} d∉vs++ocurrM·N
    d∉M : d ∉ M
    d∉M = lemmaocurr (c∉xs++ys→c∉xs {d} {ocurr M} {ocurr N} (c∉xs++ys→c∉ys {d} {vs} {ocurr (M · N)} d∉vs++ocurrM·N)) 
    d∉N : d ∉ N
    d∉N = lemmaocurr (c∉xs++ys→c∉ys {d} {ocurr M} {ocurr N} (c∉xs++ys→c∉ys {d} {vs} {ocurr (M · N)} d∉vs++ocurrM·N)) 
    （ac）M∼α（bc）N : （ a ∙ c ） M ∼α （ b ∙ c ） N
    （ac）M∼α（bc）N =  begin
                         （ a ∙ c ） M 
                       ∼⟨ σ (lemma∙ c#λaM d∉M) ⟩
                         （ d ∙ c ） （ a ∙ d ） M 
                       ∼⟨ lemma∼αEquiv [(d , c)] (fα d d∉vs) ⟩
                         （ d ∙ c ） （ b ∙ d ） N
                       ∼⟨ lemma∙ c#λbN d∉N ⟩
                         （ b ∙ c ） N
                       ∎
\end{code}





