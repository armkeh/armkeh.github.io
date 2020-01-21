module EqualityOfFunctions where

open import Data.Nat using (ℕ ; zero ; suc ; _+_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl)
open Eq.≡-Reasoning using (begin_ ; _≡⟨⟩_ ; _≡⟨_⟩_ ; _∎)

open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Product using (_,_ ; uncurry)
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; sym ; cong ; cong-app)
open Eq.≡-Reasoning using (begin_ ; _≡⟨⟩_ ; _≡⟨_⟩_ ; _∎)

record PseudoAddition : Set where
  field
    _⊕_ : ℕ → ℕ → ℕ
    z⊕n≡n : (n : ℕ) → zero ⊕ n ≡ n
    [suc-m]⊕n≡suc-[m⊕n] : (m n : ℕ) → (suc m) ⊕ n ≡ suc (m ⊕ n)

  m⊕n≡m+n : (m n : ℕ) →  m ⊕ n ≡ m + n
  m⊕n≡m+n zero n = z⊕n≡n n
  m⊕n≡m+n (suc m) n =
    begin
      (suc m ⊕ n)
    ≡⟨ [suc-m]⊕n≡suc-[m⊕n] m n ⟩
      suc (m ⊕ n)
    ≡⟨ cong suc (m⊕n≡m+n m n) ⟩
      suc (m + n)
    ∎

_+′_ : ℕ → ℕ → ℕ
m +′ n = m + n + 0

+′-is-PseudoAddition : PseudoAddition
+′-is-PseudoAddition =
  record { _⊕_ = _+′_
         ; z⊕n≡n = +-identityʳ
         ; [suc-m]⊕n≡suc-[m⊕n] = λ _ _ → refl }

m+′n≡m+n : (m n : ℕ) → m +′ n ≡ m + n
m+′n≡m+n = PseudoAddition.m⊕n≡m+n +′-is-PseudoAddition

_+″_ : ℕ → ℕ → ℕ
zero  +″ n = n
suc m +″ n = suc (m +″ n)

_+‴_ : ℕ → ℕ → ℕ
m +‴ n = m + n

+‴≡+ : _+‴_ ≡ _+_
+‴≡+ = refl

disagree : {A B : Set} → {f g : A → B}
         → (x : A) → ¬ f x ≡ g x → ¬ f ≡ g
disagree x fx≢gx refl = fx≢gx refl

record NotAddition-zero : Set where
  field
    _⊕_ : ℕ → ℕ → ℕ
    n : ℕ
    ¬z⊕n≡n : ¬ (zero ⊕ n ≡ n)

  ¬a⊕b≡a+b : ¬ ((a b : ℕ) → a ⊕ b ≡ a + b)
  ¬a⊕b≡a+b a⊕b≡a+b = ¬z⊕n≡n (a⊕b≡a+b zero n)

  ¬⊕≡+ : ¬ _⊕_ ≡ _+_
  ¬⊕≡+ ⊕≡+ = ¬z⊕n≡n z⊕n≡n
    where
      z⊕n≡n : zero ⊕ n ≡ n
      z⊕n≡n =
        begin
          zero ⊕ n
        ≡⟨⟩
          uncurry _⊕_ (zero , n)
        ≡⟨ cong (λ x → uncurry x (zero , n)) ⊕≡+ ⟩
          uncurry _+_ (zero , n)
        ≡⟨⟩
          n
        ∎

record NotAddition-suc : Set where
  field
    _⊕_ : ℕ → ℕ → ℕ
    m n : ℕ
    ¬[suc-m]⊕n≡suc-[m⊕n] : ¬ ((suc m) ⊕ n ≡ suc (m ⊕ n))

  ¬a⊕b≡a+b : ¬ ((a b : ℕ) → a ⊕ b ≡ a + b)
  ¬a⊕b≡a+b a⊕b≡a+b = ¬[suc-m]⊕n≡suc-[m⊕n] [suc-m]⊕n≡suc-[m⊕n]
    where
      [suc-m]⊕n≡suc-[m⊕n] : (suc m) ⊕ n ≡ suc (m ⊕ n)
      [suc-m]⊕n≡suc-[m⊕n] =
        begin
          (suc m) ⊕ n
        ≡⟨ a⊕b≡a+b (suc m) n ⟩
          (suc m) + n
        ≡⟨⟩
          suc (m + n)
        ≡⟨ cong suc (sym (a⊕b≡a+b m n)) ⟩
          suc (m ⊕ n)
        ∎

  ¬⊕≡+ : ¬ _⊕_ ≡ _+_
  ¬⊕≡+ ⊕≡+ = ¬[suc-m]⊕n≡suc-[m⊕n] [suc-m]⊕n≡suc-[m⊕n]
    where
      [suc-m]⊕n≡suc-[m⊕n] : (suc m) ⊕ n ≡ suc (m ⊕ n)
      [suc-m]⊕n≡suc-[m⊕n] =
        begin
          (suc m) ⊕ n
        ≡⟨⟩
          uncurry _⊕_ (suc m , n)
        ≡⟨ cong (λ x → uncurry x (suc m , n)) ⊕≡+ ⟩
          uncurry _+_ (suc m , n)
        ≡⟨⟩
          suc (uncurry _+_ (m , n))
        ≡⟨ cong (λ x → suc (uncurry x (m , n))) (sym ⊕≡+) ⟩
          suc (uncurry _⊕_ (m , n))
        ≡⟨⟩
          suc (m ⊕ n)
        ∎
