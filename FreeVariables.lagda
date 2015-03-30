\begin{code}
module FreeVariables where

open import Atom
open import Alpha
open import ListProperties
open import Term hiding (fv)
open import TermRecursion
open import TermInduction
open import TermAcc
open import NaturalProperties
open import Equivariant
open import Permutation

open import Data.Bool hiding (_∨_)
open import Data.Nat hiding (_*_)
open import Data.Nat.Properties
open import Data.Empty
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.List
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership
open Any.Membership-≡
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable

\end{code}

%<*freeVariables>
\begin{code}
fv : Λ → List Atom
fv = ΛIt (List Atom) [_] _++_ ([] , λ v r → r - v)
\end{code}
%</freeVariables>

\begin{code}
lemmafv· : ∀ M N → fv (M · N) ≡  fv M ++ fv N
lemmafv· M N = refl
--
lemmafvƛ : ∀ b M → fv (ƛ b M) ≡ fv (（ b ∙ χ [] (ƛ b M) ） M) - χ [] (ƛ b M)
lemmafvƛ b M = ΛItƛ (List Atom) [_] _++_ []  (λ v r → r - v) b M
--
lemma∼αfv : {M N : Λ} → M ∼α N → fv M ≡ fv N
lemma∼αfv {M} {N} = lemmaItαStrongCompatible (List Atom) [_] _++_ [] (λ v r → r - v) M N 
--
\end{code}

%<*fvPred>
\begin{code}
Pfv* : Atom → Λ → Set
Pfv* a M = a ∈ fv M → a * M
\end{code}
%</fvPred>

\begin{code}
αCompatiblePfv* : ∀ a → αCompatiblePred (Pfv* a)
αCompatiblePfv* a M∼αN a∈fvM→a*M a∈fvN 
  rewrite lemma∼αfv M∼αN = lemma∼α* M∼αN (a∈fvM→a*M a∈fvN)
--
lemmafv* : ∀ {a} {M} → Pfv* a M
lemmafv* {a} {M} = TermαIndPerm (Pfv* a) (αCompatiblePfv* a) lemmav lemma· lemmaƛ M
  where
  lemmav : (b : Atom) → Pfv* a (v b)
  lemmav .a  (here refl) = *v
  lemmav b   (there ()) 
  lemma· : (M N : Λ) → Pfv* a M → Pfv* a N → Pfv* a (M · N)
  lemma· M N PM PN a∈fvM·N rewrite lemmafv· M N  
    with c∈xs++ys→c∈xs∨c∈ys {a} {fv M} {fv N} a∈fvM·N 
  ... | inj₁ a∈fvM = *·l (PM a∈fvM)
  ... | inj₂ a∈fvN = *·r (PN a∈fvN)
  lemmaƛ : Σ (List ℕ) (λ xs → (M : Λ) (b : ℕ) → b ∉ xs → (∀ π → Pfv* a (π ∙ M)) → Pfv* a (ƛ b M))
  lemmaƛ = [ a ] , lemmaƛaux
    where 
    lemmaƛaux : (M : Λ) (b : ℕ) → b ∉ [ a ] → (∀ π → Pfv* a (π ∙ M)) → Pfv* a (ƛ b M)
    lemmaƛaux M b b∉[a] f a∈fvƛbM 
      rewrite lemmafvƛ b M
      with χ [] (ƛ b M) | lemmafilter→ a (fv (（ b ∙ χ [] (ƛ b M) ） M)) (λ y → not (⌊ χ [] (ƛ b M) ≟ₐ y ⌋)) a∈fvƛbM  | χ# [] (ƛ b M)
    ... | c | ¬a≟c=true , a∈fv（bc）M | c#ƛbM with a ≟ₐ c
    lemmaƛaux M b b∉[a] f a∈fvƛbM | .a | ¬a≟a=true , a∈fv（ba）M | c#ƛbM | yes refl with a ≟ₐ a
    lemmaƛaux M b b∉[a] f a∈fvƛbM | .a | () , a∈fv（ba）M | c#ƛbM | yes refl | yes _
    lemmaƛaux M b b∉[a] f a∈fvƛbM | .a | _ , a∈fv（ba）M | c#ƛbM | yes refl | no a≢a = ⊥-elim (a≢a refl)
    lemmaƛaux M b b∉[a] f a∈fvƛbM | c  | _ , a∈fv（bc）M | c#ƛbM | no a≢c 
      = *ƛ (lemma*swap←≢ (sym≢ b≢a) a≢c  (f [(b , c)] a∈fv（bc）M)) b≢a
      where
      b≢a : b ≢ a
      b≢a = λ b≡a → (⊥-elim (b∉[a] (here b≡a)))
\end{code}
