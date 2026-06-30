------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on DiffList
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.DifferenceList.Properties where

open import Data.DifferenceList.Base
open import Data.List as List using (List)
import Data.List.Properties as List
open import Data.Product using (Σ-syntax; _,_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; module ≡-Reasoning)

open ≡-Reasoning

private
  variable
    a b : Level
    A : Set a
    B : Set b
    xs xs₁ xs₂ : List A
    ys ys₁ ys₂ : DiffList A

-- ≈ is bisimulation between List and DiffList
infix 1 _≈_
_≈_ : {A : Set a} → List A → DiffList A → Set a
_≈_ {A = A} xs ys = (k : List A) → xs List.++ k ≡ ys k

IsAppend : {A : Set a} → DiffList A → Set a
IsAppend {A = A} ys = Σ[ xs₁ ∈ List A ] (∀ xs₂ → ys xs₂ ≡ xs₁ List.++ xs₂)

fromList∘toList : IsAppend ys → ∀ k → fromList (toList ys) k ≡ ys k
fromList∘toList {ys = ys} (xs₁ , p) k = begin
  fromList (toList ys) k          ≡⟨⟩
  ys List.[] List.++ k            ≡⟨ cong (List._++ k) (p List.[]) ⟩
  (xs₁ List.++ List.[]) List.++ k ≡⟨ cong (List._++ k) (List.++-identityʳ xs₁) ⟩
  xs₁ List.++ k                   ≡⟨ sym (p k) ⟩
  ys k                            ∎

toList∘fromList : toList (fromList xs) ≡ xs
toList∘fromList {xs = xs} = List.++-identityʳ xs

open import Data.Product using (Σ; proj₁)
open import Function.Bundles
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality using (_≗_)
open import Function using (_on_)
open import Relation.Binary.Construct.On
open import Relation.Binary.PropositionalEquality.Properties renaming (setoid to ≡-setoid)
-- open import Relation.Binary.PropositionalEquality.Properties renaming (setoid to ≡-setoid)
-- open import Function.Indexed.Relation.Binary.Equality using (≡-setoid)
DiffListSetoid : Set a → Setoid {!!} {!!}
DiffListSetoid A = record { Carrier = Σ (DiffList A) IsAppend ; _≈_ = _≗_ on proj₁ ; isEquivalence = record { refl = λ {x} x₁ → refl ; sym = λ x x₁ → {!!} ; trans = {!!} } }
a1 : {A : Set a} → Inverse (≡-setoid (List A)) {!!}
a1 = {!!}

-- `lift` respects `≈` when `f` is a prepend
lift⁺ : (f : List A → List A) →
        (∀ xs′ → f xs′ ≡ f List.[] List.++ xs′) →
        xs ≈ ys →
        f xs ≈ lift f ys
lift⁺ {xs = xs} {ys = ys} f f-is-prepend sim k = begin
  f xs List.++ k                   ≡⟨ cong (List._++ k) (f-is-prepend xs) ⟩
  (f List.[] List.++ xs) List.++ k ≡⟨ List.++-assoc (f List.[]) xs k ⟩
  f List.[] List.++ (xs List.++ k) ≡⟨ sym (f-is-prepend (xs List.++ k)) ⟩
  f (xs List.++ k)                 ≡⟨ cong f (sim k) ⟩
  f (ys k)                         ≡⟨⟩
  lift f ys k                      ∎

[]⁺ : List.[] {A = A} ≈ []
[]⁺ k = refl

∷⁺ : (x : A) → xs ≈ ys → x List.∷ xs ≈ x ∷ ys
∷⁺ x sim = lift⁺ (x List.∷_) (λ _ → refl) sim

[_]⁺ : (x : A) → List.[ x ] ≈ [ x ]
[_]⁺ x k = refl

++⁺ : xs₁ ≈ ys₁ → xs₂ ≈ ys₂ → xs₁ List.++ xs₂ ≈ ys₁ ++ ys₂
++⁺ {xs₁ = xs₁} {ys₁ = ys₁} {xs₂ = xs₂} {ys₂ = ys₂} sim₁ sim₂ k = begin
  (xs₁ List.++ xs₂) List.++ k ≡⟨ List.++-assoc xs₁ xs₂ k ⟩
  xs₁ List.++ (xs₂ List.++ k) ≡⟨ cong (xs₁ List.++_) (sim₂ k) ⟩
  xs₁ List.++ ys₂ k           ≡⟨ sim₁ (ys₂ k) ⟩
  ys₁ (ys₂ k)                 ≡⟨⟩
  (ys₁ ++ ys₂) k              ∎

++-∷⁺ : (x : A) → xs₁ ≈ ys₁ → xs₂ ≈ ys₂ →
        xs₁ List.++ x List.∷ xs₂ ≈ ys₁ ++ x ∷ ys₂
++-∷⁺ x sim₁ sim₂ = ++⁺ sim₁ (∷⁺ x sim₂)

∷ʳ⁺ : (x : A) → xs ≈ ys → xs List.∷ʳ x ≈ ys ∷ʳ x
∷ʳ⁺ {xs = xs} {ys} x sim k = begin
  xs List.∷ʳ x List.++ k            ≡⟨⟩
  (xs List.++ List.[ x ]) List.++ k ≡⟨ List.++-assoc xs List.[ x ] k ⟩
  xs List.++ (x List.∷ k)           ≡⟨ sim (x List.∷ k) ⟩
  ys (x List.∷ k)                   ≡⟨⟩
  (ys ∷ʳ x) k                       ∎

toList⁺ : xs ≈ ys → xs ≡ toList ys
toList⁺ {xs = xs} {ys} sim = begin
  xs                 ≡⟨ sym (List.++-identityʳ xs) ⟩
  xs List.++ List.[] ≡⟨ sim List.[] ⟩
  ys List.[]         ≡⟨⟩
  toList ys          ∎

fromList⁺ : xs ≈ ys → ∀ k → fromList xs k ≡ ys k
fromList⁺ sim k = sim k

map⁺ : (f : A → B) → xs ≈ ys →
       List.map f xs ≈ map f ys
map⁺ {xs = xs} {ys} f sim k = begin
  List.map f xs List.++ k
    ≡⟨ cong (λ xs → List.map f xs List.++ k) (sym (List.++-identityʳ xs)) ⟩
  List.map f (xs List.++ List.[]) List.++ k
    ≡⟨ cong (λ xs → List.map f xs List.++ k) (sim List.[]) ⟩
  List.map f (ys List.[]) List.++ k
    ≡⟨⟩
  map f ys k ∎
