module Q where

open import Data.Bool hiding (not)
open import Data.Nat hiding (_+_; _*_)
open import Data.Product hiding (map)
open import Data.List hiding (map; zipWith)
open import Data.Vec 
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

------------------------------------------------------------------------------
-- Bare scalars

data Scalar : Set where
  <+1> : Scalar
  <-1> : Scalar
  <0>  : Scalar

_+_ : Scalar → Scalar → Scalar
<0> + s₂ = s₂
<+1> + <-1> = <0>
<+1> + <+1> = <+1>
<+1> + <0> = <+1>
<-1> + <+1> = <0>
<-1> + <-1> = <-1> 
<-1> + <0> = <-1>

_*_ : Scalar → Scalar → Scalar
<+1> * s₂ = s₂
<-1> * <+1> = <-1>
<-1> * <-1> = <+1>
<-1> * <0> = <0>
<0> * s₂ = <0> 

-- Example proofs

*unitRight : ∀ s → s * <+1> ≡ s
*unitRight <+1> = refl
*unitRight <-1> = refl
*unitRight <0> = refl 

simplify1 : ∀ sf st → ((<-1> * ((<-1> * sf) + st)) + (sf + st)) ≡ sf
simplify1 <+1> <+1> = refl
simplify1 <+1> <-1> = refl
simplify1 <+1> <0> = refl
simplify1 <-1> <+1> = refl
simplify1 <-1> <-1> = refl
simplify1 <-1> <0> = refl
simplify1 <0> <+1> = refl
simplify1 <0> <-1> = refl
simplify1 <0> <0> = refl

simplify2 : ∀ sf st → (((<-1> * sf) + st) + (sf + st)) ≡ st
simplify2 <+1> <+1> = refl
simplify2 <+1> <-1> = refl
simplify2 <+1> <0> = refl
simplify2 <-1> <+1> = refl
simplify2 <-1> <-1> = refl
simplify2 <-1> <0> = refl
simplify2 <0> <+1> = refl
simplify2 <0> <-1> = refl
simplify2 <0> <0> = refl

------------------------------------------------------------------------------
-- Vectors

V : ℕ → Set
V n = Vec Scalar n

_*>_ : ∀ {n} → Scalar → V n → V n
s *> v = map (λ s' → s * s') v

_⊕_ : ∀ {n} → V n → V n → V n
v₁ ⊕ v₂ = zipWith _+_ v₁ v₂

------------------------------------------------------------------------------
-- Gates

Qubit : Set
Qubit = V 2

Had : Bool → Qubit
Had false = <-1> ∷ <+1> ∷ []
Had true  = <+1> ∷ <+1> ∷ []

HadQ : Qubit → Qubit
HadQ (sf ∷ st ∷ []) = (sf *> Had false) ⊕ (st *> Had true) 

-- Example proofs

Had1 : ∀ sf st → HadQ (sf ∷ st ∷ []) ≡ (((<-1> * sf) + st) ∷ (sf + st) ∷ [])
Had1 <+1> <+1> = refl
Had1 <+1> <-1> = refl
Had1 <+1> <0> = refl
Had1 <-1> <+1> = refl
Had1 <-1> <-1> = refl
Had1 <-1> <0> = refl
Had1 <0> <+1> = refl
Had1 <0> <-1> = refl
Had1 <0> <0> = refl 

Had²≡id : ∀ x → HadQ (HadQ x) ≡ x
Had²≡id (sf ∷ st ∷ []) = begin
  HadQ (HadQ (sf ∷ st ∷ []))
    ≡⟨ cong HadQ (Had1 sf st) ⟩
  HadQ (((<-1> * sf) + st) ∷ (sf + st) ∷ [])
    ≡⟨ Had1 ((<-1> * sf) + st) (sf + st) ⟩
  (((<-1> * ((<-1> * sf) + st)) + (sf + st)) ∷ (((<-1> * sf) + st) + (sf + st)) ∷ [])
    ≡⟨ cong₂ (λ h₁ h₂ → h₁ ∷ h₂ ∷ []) (simplify1 sf st) (simplify2 sf st) ⟩ 
  (sf ∷ st ∷ []) ∎

------------------------------------------------------------------------------

{--
-- can reason with errors
-- add intervals of confidence for scalars
-- invtervals of confidence for the gates
-- monads in background to make intervals transparent
--}
