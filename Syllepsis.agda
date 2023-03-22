{-# OPTIONS --cubical #-}

module Syllepsis where

-- agda/cubical library
open import Cubical.Foundations.Prelude
  using ( Level ; Type ; PathP ; Path ; _≡_ ; refl
        ; hcomp ; i0 ; i1 ; _∧_ ; _∨_ ; ~_
        ; cong ; sym ; _∙_ ; _≡⟨_⟩_ ; _∎
        )
open import Cubical.HITs.S2 using ( S² ; base ; surf )
open import Cubical.HITs.S3 using ( S³ ; base ; surf )
open import Cubical.Foundations.GroupoidLaws using ( rCancel )

private
  variable
    ℓ : Level
    A : Type ℓ
    x : A

Ω Ω² Ω³ Ω⁴ : (A : Type ℓ) → A → Type ℓ
Ω A x = Path A x x
Ω² A x = Ω (Ω A x) refl
Ω³ A x = Ω (Ω² A x) refl
Ω⁴ A x = Ω (Ω³ A x) refl

-- commutative square of loops
1+1-cell : (α β : Ω A x) → Type _
1+1-cell α β = PathP (λ i → α i ≡ α i) β β

-- higher analogue, modeled after the 4-cell in J₂S²... apparently,
-- elements of this type are trivializations of the Whitehead product
-- of the two given loops (this is also true of the 1+1-cell I
-- suppose?)
2+2-cell : (α β : Ω² A x) → Type _
2+2-cell {A = A} α β =
  PathP (λ i → PathP (λ j → PathP (λ a → PathP (λ b → A)
                                               (α i j)
                                               (α i j))
                                  refl
                                  refl)
                     (λ a b → β a b)
                     (λ a b → β a b))
        refl
        refl

-- "cubical Eckmann-Hilton." This induces a proof of the usual
-- statement of EH in the obvious way.
cubicalEH : (α β : Ω² A x) → 1+1-cell {A = Ω A x} α β
cubicalEH {A = A} {x = x} α β i j k =
  hcomp (λ l → λ { (i = i0) → β j (k ∧ l)
                 ; (i = i1) → β j (k ∧ l)
                 ; (j = i0) → α i k
                 ; (j = i1) → α i k
                 ; (k = i0) → x
                 ; (k = i1) → β j l
                 })
        (α i k)

-- Loop spaces always have the 2+2-cell too. (Perhaps this could
-- already be called syllepsis? But another step will be convenient.)
2+2-thingy : (α β : Ω³ A x) → 2+2-cell {A = Ω A x} α β
2+2-thingy {A = A} {x = x} α β i j a b z =
  hcomp (λ f → λ { (z = i0) → β a b (~ f)
                 ; (z = i1) → α i j f
                 ; (i = i0) → β a b (z ∨ ~ f)
                 ; (i = i1) → β a b (z ∨ ~ f)
                 ; (j = i0) → β a b (z ∨ ~ f)
                 ; (j = i1) → β a b (z ∨ ~ f)
                 ; (a = i0) → α i j (z ∧ f)
                 ; (a = i1) → α i j (z ∧ f)
                 ; (b = i0) → α i j (z ∧ f)
                 ; (b = i1) → α i j (z ∧ f)
                 })
        x

-- This gives us a "cubical syllepsis" stated in terms of the
-- _transposition_ of the EH commutative square. This does induce a
-- proof of the usual statement of syllepsis, but it's a bit ugly and
-- I won't do it here.
cubicalSyllepsis : (α β : Ω³ A x)
  → cubicalEH α β ≡ (λ i j → cubicalEH β α j i)
cubicalSyllepsis {A = A} α β f i j k =
  hcomp (λ l → λ { (i = i0) → β j (k ∧ (l ∨ f))
                 ; (i = i1) → β j (k ∧ (l ∨ f))
                 ; (j = i0) → α i (k ∧ (l ∨ ~ f))
                 ; (j = i1) → α i (k ∧ (l ∨ ~ f))
                 ; (k = i0) → refl
                 ; (k = i1) → 2+2-thingy α β i (l ∨ ~ f) j (l ∨ f)
                 })
        (2+2-thingy α β i (k ∧ ~ f) j (k ∧ f))

-- Now we need a couple lemmas.

-- First, the inverse to the "constSquare" equivalence
constSquareInv : {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → PathP (λ i → p i ≡ q i) p q
  → Ω² A y
constSquareInv p q r i j =
  hcomp (λ k → λ { (i = i0) → p (k ∨ j)
                 ; (i = i1) → q (~ k ∧ j)
                 ; (j = i0) → p (k ∨ i)
                 ; (j = i1) → q (~ k ∧ i)
                 })
        (r i j)

-- Second, transposition of 2-loops is equal to inversion/symmetry
transposeInv : (p : Ω² A x)
  → Path (Ω² A x)
         (λ j k → p k j)
         (λ j k → p (~ j) k)
transposeInv p i j k =
  hcomp (λ l → λ { (i = i0) → p k j
                 ; (i = i1) → p (~ j) k
                 ; (j = i0) → p (i ∨ k ∨ l) (i ∧ k)
                 ; (j = i1) → p (~ i ∧ k ∧ ~ l) (~ i ∨ k)
                 ; (k = i0) → p (i ∧ ~ j ∧ ~ l) (~ i ∧ j)
                 ; (k = i1) → p (~ i ∨ ~ j ∨ l) (i ∨ j)
                 })
        (p ((~ j ∧ k) ∨ (i ∧ ~ j) ∨ (~ i ∧ k)) ((j ∧ k) ∨ (~ i ∧ j) ∨ (i ∧ k)))

-- Now, using constSquareInv, the cubical Eckmann-Hilton induces a
-- generator of π₃S²
gen-π₃S² : Ω³ S² base
gen-π₃S² = constSquareInv surf surf (cubicalEH surf surf)

-- It also induces a generator of π₄S³
gen-π₄S³ : Ω⁴ S³ base
gen-π₄S³ = constSquareInv surf surf (cubicalEH surf surf)

-- Now, relying on the nice symmetry of constSquareInv under
-- transposition, the cubical syllepsis immediately implies that
-- gen-π₄S³ is equal to its own transpose, and thus it is equal to its
-- own inverse:
gen-π₄S³-sym =
  gen-π₄S³
    ≡⟨ cong (constSquareInv surf surf) (cubicalSyllepsis surf surf) ⟩
  (λ i j → gen-π₄S³ j i)
    ≡⟨ transposeInv gen-π₄S³ ⟩
  sym gen-π₄S³
    ∎

-- Therefore it has order 2:
gen-π₄S³-order =
  gen-π₄S³ ∙ gen-π₄S³
    ≡⟨ cong (gen-π₄S³ ∙_) gen-π₄S³-sym ⟩
  gen-π₄S³ ∙ sym gen-π₄S³
    ≡⟨ rCancel gen-π₄S³ ⟩
  refl
    ∎
