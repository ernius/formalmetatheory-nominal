\begin{code}
module TermInduction where

open import Atom
open import Alpha
open import ListProperties
open import Term
open import Chi
open import TermAcc
open import NaturalProperties
open import Permutation

open import Level
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.List
open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership
open Any.Membership-≡
open import Relation.Binary.PropositionalEquality hiding ([_])

\end{code}

Primitive induction over raw terms:

%<*termPrimInduction>
\begin{code}
TermPrimInd : {l : Level}(P : Λ → Set l) 
  → (∀ a → P (v a))
  → (∀ M N → P M → P N → P (M · N))
  → (∀ M b → P M → P (ƛ b M))
  → ∀ M → P M
\end{code}
%</termPrimInduction>

\begin{code}
TermPrimInd P ha h· hƛ (v a)    
  = ha a
TermPrimInd P ha h· hƛ (M · N)  
  = h· M N (TermPrimInd P ha h· hƛ M) (TermPrimInd P ha h· hƛ N)
TermPrimInd P ha h· hƛ (ƛ a M)  
  = hƛ M a (TermPrimInd P ha h· hƛ M)
\end{code}

\begin{code}
lemmavIndSw : {l : Level}{P : Λ → Set l} → (∀ a → P (v a)) → ∀ a π → P (π ∙ v a)
lemmavIndSw hv a π rewrite lemmaπv {a} {π} = hv ( π ∙ₐ a)
--
lemma·IndSw : {l : Level}{P : Λ → Set l} 
  → (∀ M N → P M → P N →  P (M · N))
  → (M N : Λ)
  →  ((π : Π) → P (π ∙ M))
  →  ((π : Π) → P (π ∙ N)) 
  →  (π : Π) → P (π ∙ M · N)
lemma·IndSw h· M N fM fN π rewrite lemmaπ· {M} {N} {π} 
  = h· (π ∙ M) (π ∙ N) (fM π) (fN π)
--
lemmaƛIndSw :  {l : Level}{P : Λ → Set l}
  → (∀ M b → (∀ π → P (π ∙ M)) → P (ƛ b M))  
  → (M : Λ) (a : ℕ) 
  → ((π : List (Atom × Atom)) → P (π ∙ M)) 
  → (π : List (Atom × Atom)) → P (π ∙ ƛ a M)
lemmaƛIndSw {P = P} hƛ M a fM π rewrite lemmaπƛ {a} {M} {π} 
  = hƛ (π ∙ M) (π ∙ₐ a) (λ π′ → corollaryPπ++π′∙M→Pπ∙π′∙M {π} {M} {P = P} π′ (fM (π′ ++ π)))
\end{code}

Permutation induction principle proved using previous primitive recursion principle.

%<*termIndPermutation>
\begin{code}
TermIndPerm : {l : Level}(P : Λ → Set l) 
  → (∀ a → P (v a))
  → (∀ M N → P M → P N →  P (M · N))
  → (∀ M b → (∀ π → P (π ∙ M)) → P (ƛ b M))
  → ∀ M → P M
\end{code}
%</termIndPermutation>

\begin{code} 
TermIndPerm P hv h· hƛ M 
 = TermPrimInd  (λ M → ∀ π → (P (π ∙ M))) 
                (lemmavIndSw {P = P} hv) (lemma·IndSw h·) (lemmaƛIndSw {P = P} hƛ) M []
\end{code}

Prove α Primitive Ind with Swap induction.

\begin{code}
lemmaαƛPrimInd :  {l : Level}(P : Λ → Set l) → αCompatiblePred P  
  →  (vs : List Atom) 
  →  (∀ M b → b ∉ vs → P M → P (ƛ b M)) 
  →  (M : Λ) (a : ℕ) 
  →  (∀ π → P ( π ∙ M)) 
  →  P (ƛ a M)
lemmaαƛPrimInd P αP vs hƛ M a PM with χ vs (ƛ a M) | χ∉ vs (ƛ a M) | χ# vs (ƛ a M)
... | b | b∉vs | b#ƛaM = αP (σ (lemma∼αλ' b#ƛaM)) (hƛ (（ a ∙ b ） M) b b∉vs (PM [(a , b)]))
--
\end{code}

%<*alphaPrimInduction>
\begin{code}
TermαPrimInd :  {l : Level}(P : Λ → Set l) → αCompatiblePred P 
  → (∀ a → P (v a))
  → (∀ M N → P M → P N → P (M · N))
  → ∃ (λ vs → (∀ M b → b ∉ vs → P M → P (ƛ b M)))
  → ∀ M → P M
\end{code}
%</alphaPrimInduction>

\begin{code}
TermαPrimInd P αP ha h· (vs , hƛ) = TermIndPerm P ha h· (lemmaαƛPrimInd P αP vs hƛ)
\end{code}

Prove α Swap Ind with Swap Induction 

\begin{code}
lemmaαƛ :  {l : Level}(P : Λ → Set l) → αCompatiblePred P 
  →  (vs : List Atom) 
  →  (∀ M b → b ∉ vs → (∀ π →  P (π ∙ M)) → P (ƛ b M)) 
  →  (M : Λ) (a : ℕ) 
  →  (∀ π → P (π ∙ M)) 
  →  P (ƛ a M)
lemmaαƛ P αP vs hƛ M a fM with χ vs (ƛ a M) | χ∉ vs (ƛ a M) | χ# vs (ƛ a M)
... | b | b∉vs | b#ƛaM 
  = αP  (σ (lemma∼αλ' b#ƛaM)) 
        (hƛ  ([( a , b )] ∙ M) b b∉vs 
             (λ π → corollaryPπ++π′∙M→Pπ∙π′∙M {[(a , b)]} {M} {P = P} π (fM (π ++ [( a , b )])))) 
\end{code}

%<*alphaIndPermutation>
\begin{code}
TermαIndPerm : {l : Level}(P : Λ → Set l) → αCompatiblePred P 
  → (∀ a → P (v a))
  → (∀ M N → P M → P N →  P (M · N))
  → ∃ (λ as → (∀ M b → b ∉ as → (∀ π →  P (π ∙ M)) → P (ƛ b M)))
  → ∀ M → P M
\end{code}
%</alphaIndPermutation>

\begin{code}
TermαIndPerm P αP ha h· (vs , hƛ) = TermIndPerm P ha h· (lemmaαƛ P αP vs  hƛ)
\end{code}

Prove α ∃ Ind with Swap Induction


\begin{code}
TISw2TISwEx : {l : Level}(P : Λ → Set l) → αCompatiblePred P 
  → (∀ a → P (v a))
  → (∀ M N → P M → P N →  P (M · N))
  → (∀ M a → ∃ (λ b → Σ  (b # ƛ a M)  (λ _ → P (（ a ∙ b ） M) → P (ƛ b  (（ a ∙ b ） M)))))
  → ∀ M → P M
TISw2TISwEx P αCompP hv h· hƛ 
  = TermαIndPerm P αCompP hv h· ([] ,  lemma∃ƛ)
  where 
  lemma∃ƛ : (M : Λ) (b : ℕ) → b ∉ [] → (∀ π → P (π ∙ M)) → P (ƛ b M)
  lemma∃ƛ M b _ ∀π,PπM with hƛ M b 
  ... | a , a#λbM , P（ba）M→Pƛa（ba）M = αCompP (σ (lemma∼αλ' a#λbM)) (P（ba）M→Pƛa（ba）M (∀π,PπM [(b , a)]))  
\end{code}
