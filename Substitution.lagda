\begin{code}
module Substitution where

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
open import FreeVariables

open import Data.Bool hiding (_∨_)
open import Data.Nat hiding (_*_)
open import Data.Nat.Properties
open import Data.Empty
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.List
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership
open Any.Membership-≡ renaming (_∈_ to _∈'_;_∉_ to _∉'_) 
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable
\end{code}

%<*substitution>
\begin{code}
hvar : Atom → Λ → Atom → Λ
hvar x N y with x ≟ₐ y
... | yes _ = N
... | no  _ = v y
--
_[_:=_] : Λ → Atom → Λ → Λ
M [ a := N ] = ΛIt Λ (hvar a N) _·_ (a ∷ fv N , ƛ) M
\end{code}
%</substitution>

\begin{code}
-- Substitution behaviour under term constructors
lemmaSubst· : ∀ a M N P → (M · N) [ a := P ] ≡ M [ a := P ] · N [ a := P ]
lemmaSubst· a M N P = refl
--
lemmaSubstƛ : ∀ a b M P → (ƛ b M) [ a := P ] ≡ ƛ (χ (a ∷ fv P) (ƛ b M)) ( ( （ b ∙ (χ (a ∷ fv P) (ƛ b M)) ） M) [ a := P ] )
lemmaSubstƛ a b M P = ΛItƛ Λ (hvar a P) _·_ (a ∷ fv P)  ƛ b M
--
lemmahvar : {a b : Atom}{M : Λ} → a ≡ b × hvar a M b ≡ M ∨ a ≢ b × hvar a M b ≡ v b
lemmahvar {a} {b} {M} with a ≟ₐ b
lemmahvar {a} {.a}  {M}  | yes  refl  = inj₁ (refl , refl)
lemmahvar {a} {b}   {M}  | no   a≢b   = inj₂ (a≢b , refl)
--
lemmahvar≡ : {a : Atom}{M : Λ} → hvar a M a ≡ M
lemmahvar≡ {a} {M} with lemmahvar {a} {a} {M}
... | inj₁ (_    , hvaraMa≡a)  = hvaraMa≡a
... | inj₂ (a≢a  , _      )    = ⊥-elim (a≢a refl)
--
lemmahvar≢ : {a b : Atom}{M : Λ} → a ≢ b → hvar a M b ≡ v b
lemmahvar≢ {a} {b} {M} a≢b with lemmahvar {a} {b} {M}
... | inj₁ (a≡b    , _)       = ⊥-elim (a≢b a≡b)
... | inj₂ (_  , hvaraMb≡b )  = hvaraMb≡b
\end{code}

%<*lemmaSubst1>
\begin{code}
lemmaSubst1 : {M N : Λ}(P : Λ)(a : Atom) 
  → M ∼α N → M [ a := P ] ≡ N [ a := P ]
\end{code}
%</lemmaSubst1>

\begin{code}
lemmaSubst1 {M} {N} P a = lemmaItαStrongCompatible Λ (hvar a P) _·_  (a ∷ fv P) ƛ M N 
\end{code}


\begin{code}
import Relation.Binary.PreorderReasoning as PreR
open PreR ≈-preorder
--
Ps : Λ → Λ → Atom → Λ → Set
Ps N P x M = N ∼α P → M [ x := N ] ∼α M [ x := P ]
--
\end{code}

%<*lemmaSubst2>
\begin{code}
lemmaSubst2 : ∀ {N} {P} M x 
  → N ∼α P → M [ x := N ] ∼α M [ x := P ]
\end{code}
%</lemmaSubst2>

\begin{code}
lemmaSubst2 {N} {P} M x = TermIndPerm (Ps N P x) lemmav lemma· lemmaƛ M
  where
  lemmav : (a : Atom) → Ps N P x (v a)
  lemmav a N∼αP with x ≟ₐ a
  ... | yes _ = N∼αP
  ... | no  _ = ∼αv
  lemma· : (M M' : Λ) → (Ps N P x) M → Ps N P x M' → Ps N P x (M · M')
  lemma· M M' PsM PsM' N∼αP 
    rewrite  lemmaSubst· x M M' N 
    |        lemmaSubst· x M M' P 
    = ∼α· (PsM N∼αP) (PsM' N∼αP) 
  lemmaƛ :  (M : Λ) (b : Atom) → (∀ π → Ps N P x (π ∙ M)) → Ps N P x (ƛ b M)
  lemmaƛ M b f N∼P 
    = begin
        ƛ b M [ x := N ] 
      ≈⟨ lemmaSubstƛ x b M N ⟩
        ƛ c ((（ b ∙ c ） M) [ x := N ])
      ∼⟨ lemma∼αƛ (f [(b , c)] N∼P) ⟩
        ƛ c ((（ b ∙ c ） M) [ x := P ])
      ≈⟨ cong (λ y → ƛ y ((（ b ∙ y ） M) [ x := P ])) c≡d ⟩
        ƛ d ((（ b ∙ d ） M) [ x := P ])
      ≈⟨ sym (lemmaSubstƛ x b M P) ⟩
        ƛ b M [ x := P ]
      ∎
    where 
    c = χ (x ∷ fv N) (ƛ b M)
    c#ƛbM = χ# (x ∷ fv N) (ƛ b M)
    d = χ (x ∷ fv P) (ƛ b M)
    c≡d : c ≡ d
    c≡d rewrite lemma∼αfv N∼P = refl
\end{code}

%<*lemmaSubst>
\begin{code}
lemmaSubst : {M N P Q : Λ}(a : Atom) 
  → M ∼α N → P ∼α Q 
  → M [ a := P ] ∼α N [ a := Q ]
lemmaSubst {M} {N} {P} {Q} a M∼N P∼Q 
  =  begin
       M [ a := P ]
     ≈⟨ lemmaSubst1 P a M∼N ⟩
       N [ a := P ]
     ∼⟨ lemmaSubst2 N a P∼Q  ⟩
       N [ a := Q ]
     ∎
\end{code}
%</lemmaSubst>




    



