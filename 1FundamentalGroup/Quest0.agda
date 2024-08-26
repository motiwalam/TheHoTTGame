-- ignore
module 1FundamentalGroup.Quest0 where
open import 1FundamentalGroup.Preambles.P0

Refl : base ≡ base
Refl = λ i → base

Flip : Bool → Bool
Flip false = true
Flip true = false

flipIso : Bool ≅ Bool
flipIso = iso Flip Flip rightInv leftInv where

    rightInv : section Flip Flip
    rightInv false = λ i → false
    rightInv true = λ i → true

    leftInv : retract Flip Flip
    leftInv false = λ i → false
    leftInv true = λ i → true
    
flipPath : Bool ≡ Bool
flipPath = isoToPath flipIso

doubleCover : S¹ → Type
doubleCover base = Bool
doubleCover (loop i) = flipPath i

endPtOfTrue : base ≡ base → doubleCover base
endPtOfTrue p = endPt doubleCover p true

Refl≢loop : Refl ≡ loop → ⊥
Refl≢loop p = true≢false (cong endPtOfTrue p)

------------------- Side Quest - Empty -------------------------

toEmpty : (A : Type) → Type
toEmpty A = A → ⊥

pathEmpty : (A : Type) → Type₁
pathEmpty A = A ≡ ⊥

isoEmpty : (A : Type) → Type
isoEmpty A = A ≅ ⊥

outOf⊥ : (A : Type) → ⊥ → A
outOf⊥ A ()

toEmpty→isoEmpty : (A : Type) → toEmpty A → isoEmpty A
toEmpty→isoEmpty A f = iso f (outOf⊥ A)
                        (λ b i → outOf⊥ (f (outOf⊥ A b) ≡ b) b i) 
                        (λ a i → outOf⊥ (outOf⊥ A (f a) ≡ a) (f a) i)

isoEmpty→pathEmpty : (A : Type) → isoEmpty A → pathEmpty A
isoEmpty→pathEmpty A = isoToPath

pathEmpty→toEmpty : (A : Type) → pathEmpty A → toEmpty A
pathEmpty→toEmpty A p x = pathToFun p x


------------------- Side Quests - true≢false --------------------

true≢false' : true ≡ false → ⊥
true≢false' p = pathToFun (cong B p) tt where
    B : Bool → Type
    B true = ⊤
    B false = ⊥

  
  