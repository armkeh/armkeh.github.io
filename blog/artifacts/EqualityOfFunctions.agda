module EqualityOfFunctions where

open import Data.Nat using (ℕ ; zero ; suc ; _+_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl)
open Eq.≡-Reasoning using (begin_ ; _≡⟨⟩_ ; _≡⟨_⟩_ ; _∎)

open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Nat.Properties using (+-identityʳ)

open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; sym ; cong)
open Eq.≡-Reasoning using (begin_ ; _≡⟨⟩_ ; _≡⟨_⟩_ ; _∎)

record PseudoAddition : Set where
  field
    _⊕_ : ℕ → ℕ → ℕ
    z⊕n≡n : (n : ℕ) → zero ⊕ n ≡ n
    [suc-m]⊕n≡suc-[m⊕n] : (m n : ℕ) → (suc m) ⊕ n ≡ suc (m ⊕ n)

  {-
  m⊕n≡m+n : (m n : ℕ) →  m ⊕ n ≡ m + n
  m⊕n≡m+n zero n = z⊕n≡n n
  m⊕n≡m+n (suc m) n =
    begin
      (suc m ⊕ n)
    ≡⟨ ??? ⟩
      suc (m + n)
    ∎
  -}
  -- This was left as exercise.
  -- Uncomment and complete this definition if you intend to use this code.

_+₀_ : ℕ → ℕ → ℕ
m +₀ n = m + n + 0

+₀-is-PseudoAddition : PseudoAddition
+₀-is-PseudoAddition =
  record { _⊕_ = _+₀_
         ; z⊕n≡n = +-identityʳ
         ; [suc-m]⊕n≡suc-[m⊕n] = λ _ _ → refl }

m+₀n≡m+n : (m n : ℕ) → m +₀ n ≡ m + n
m+₀n≡m+n = PseudoAddition.m⊕n≡m+n +₀-is-PseudoAddition

_plus_ : ℕ → ℕ → ℕ
zero  plus n = n
suc m plus n = suc (m plus n)

_really-plus_ : ℕ → ℕ → ℕ
m really-plus n = m + n

really-plus≡+ : _really-plus_ ≡ _+_
really-plus≡+ = refl

disagree : {A B : Set} → {f g : A → B}
         → (witness : A) → ¬ (f witness ≡ g witness)
         → ¬ (f ≡ g)
disagree witness fw≢gw refl = fw≢gw refl

record NotAddition-zero : Set where
  field
    _⊕_ : ℕ → ℕ → ℕ
    nʷ : ℕ   -- witness
    ¬z⊕nʷ≡nʷ : ¬ (zero ⊕ nʷ ≡ nʷ)

  ¬a⊕b≡a+b : ¬ ((a b : ℕ) → a ⊕ b ≡ a + b)
  ¬a⊕b≡a+b a⊕b≡a+b = ¬z⊕nʷ≡nʷ (a⊕b≡a+b zero nʷ)

  ¬⊕≡+ : ¬ _⊕_ ≡ _+_
  ¬⊕≡+ ⊕≡+ = ¬z⊕nʷ≡nʷ z⊕n≡n
    where
      z⊕n≡n : zero ⊕ nʷ ≡ nʷ
      z⊕n≡n =
        begin
          zero ⊕ nʷ
        ≡⟨ cong (λ op → op zero nʷ) ⊕≡+ ⟩
          zero + nʷ
        ≡⟨⟩
          nʷ
        ∎

record NotAddition-suc : Set where
  field
    _⊕_ : ℕ → ℕ → ℕ
    mʷ nʷ : ℕ   -- witnesses
    ¬[suc-mʷ]⊕nʷ≡suc-[mʷ⊕nʷ] : ¬ ((suc mʷ) ⊕ nʷ ≡ suc (mʷ ⊕ nʷ))

  ¬a⊕b≡a+b : ¬ ((a b : ℕ) → a ⊕ b ≡ a + b)
  ¬a⊕b≡a+b a⊕b≡a+b = ¬[suc-mʷ]⊕nʷ≡suc-[mʷ⊕nʷ] [suc-mʷ]⊕nʷ≡suc-[mʷ⊕nʷ]
    where
      [suc-mʷ]⊕nʷ≡suc-[mʷ⊕nʷ] : (suc mʷ) ⊕ nʷ ≡ suc (mʷ ⊕ nʷ)
      [suc-mʷ]⊕nʷ≡suc-[mʷ⊕nʷ] =
        begin
          (suc mʷ) ⊕ nʷ
        ≡⟨ a⊕b≡a+b (suc mʷ) nʷ ⟩
          (suc mʷ) + nʷ
        ≡⟨⟩
          suc (mʷ + nʷ)
        ≡⟨ cong suc (sym (a⊕b≡a+b mʷ nʷ)) ⟩
          suc (mʷ ⊕ nʷ)
        ∎

  ¬⊕≡+ : ¬ _⊕_ ≡ _+_
  ¬⊕≡+ ⊕≡+ = ¬[suc-mʷ]⊕nʷ≡suc-[mʷ⊕nʷ] [suc-mʷ]⊕nʷ≡suc-[mʷ⊕nʷ]
    where
      [suc-mʷ]⊕nʷ≡suc-[mʷ⊕nʷ] : (suc mʷ) ⊕ nʷ ≡ suc (mʷ ⊕ nʷ)
      [suc-mʷ]⊕nʷ≡suc-[mʷ⊕nʷ] =
        begin
          (suc mʷ) ⊕ nʷ
        ≡⟨⟩
          suc mʷ ⊕ nʷ
        ≡⟨ cong (λ op → op (suc mʷ)  nʷ) ⊕≡+ ⟩
          suc mʷ + nʷ
        ≡⟨⟩
          suc (mʷ + nʷ)
        ≡⟨ cong (λ op → suc (op mʷ nʷ)) (sym ⊕≡+) ⟩
          suc (mʷ ⊕ nʷ)
        ≡⟨⟩
          suc (mʷ ⊕ nʷ)
        ∎
