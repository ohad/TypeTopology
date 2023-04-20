Andrew Sneap and Ohad Kammar

Ought to move under Groups eventually

\begin{code}
{-# OPTIONS --without-K --exact-split --no-sized-types --no-guardedness --auto-inline --lossy-unification --allow-unsolved-metas #-} --safe

-- TODO: remove unnecessary dependencies

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.CanonicalMap
open import Notation.Order
open import UF.PropTrunc
open import MLTT.Sigma
open import Notation.General

open import UF.Subsingletons
open import UF.FunExt
open import UF.Equiv
open import UF.Powerset
open import UF.UniverseEmbedding

-- ought to not be needed eventually
open import UF.Univalence

open import Rationals.Type
open import Rationals.Order
open import Integers.Type
open import Integers.Order

open import Groups.Type
open import Groups.GroupActions
open import Groups.Subgroups

open import MLTT.Id

open import DedekindReals.Symmetry.UF
open import DedekindReals.Symmetry.IndexedAction

module DedekindReals.Symmetry.ActionsConstructions where

  ptwise : {𝓤-X 𝓤-Y 𝓤-Z 𝓤-U 𝓤-V 𝓤-W : Universe}
    → {X : 𝓤-X ̇}
    → {Y : 𝓤-Y ̇}
    → {Z : 𝓤-Z ̇}
    → {U : 𝓤-U ̇}
    → {V : 𝓤-V ̇}
    → {W : 𝓤-W ̇}
    → (X → Y → Z) → (U → V → W) → (X × U → Y × V → Z × W)
  ptwise f g (x , u) (y , v) = (f x y) , (g u v)

  ptwise-group-structure : (G : Group 𝓤) → (H : Group 𝓥) → group-structure (⟨ G ⟩ × ⟨ H ⟩)
  ptwise-group-structure G H  = ptwise (multiplication G) (multiplication H)

  assoc-ptwise : (G : Group 𝓤) → (H : Group 𝓥) →  associative (ptwise-group-structure G H)
  assoc-ptwise G H x y z = ap2 _,_ (assoc G (pr₁ x) (pr₁ y) (pr₁ z))
                                   (assoc H (pr₂ x) (pr₂ y) (pr₂ z))
  left-neutral-ptwise : (G : Group 𝓤) → (H : Group 𝓥) →
    left-neutral (unit G , unit H) (ptwise-group-structure G H)
  left-neutral-ptwise G H x = ap2 _,_ (unit-left G (pr₁ x))
                                      (unit-left H (pr₂ x))

  right-neutral-ptwise : (G : Group 𝓤) → (H : Group 𝓥) →
    right-neutral (unit G , unit H) (ptwise-group-structure G H)
  right-neutral-ptwise G H x = ap2 _,_ (unit-right G (pr₁ x))
                                       (unit-right H (pr₂ x))
  _⊗_ : (G : Group 𝓤) → (H : Group 𝓥) → Group (𝓤 ⊔ 𝓥)
  G ⊗ H = (⟨ G ⟩ × ⟨ H ⟩) , (ptwise-group-structure G H
        , ×-is-set (group-is-set G) (group-is-set H)
        , (assoc-ptwise G H
        , ((unit G , unit H)
        , (left-neutral-ptwise G H
        , (right-neutral-ptwise G H
        , (λ {x → (inv G (pr₁ x) , inv H (pr₂ x))
               , ((ap2 _,_ (inv-left G (pr₁ x)) (inv-left H (pr₂ x)))
               ,  (ap2 _,_ (inv-right G (pr₁ x)) (inv-right H (pr₂ x))))}))))))

  ∣_×_ : {𝓥 : Universe} →
         {G H : Group 𝓤} → (A : Action' {𝓥 = 𝓥} G) →
                             (B : Action' {𝓥 = 𝓦} H) →
    Action' {𝓥 = 𝓥 ⊔ 𝓦} (G ⊗ H)
  ∣_×_ {G = G} {H} A B
    = (⟨ A ⟩ × ⟨ B ⟩)
      , ((ptwise (action-op G A) (action-op H B))
      , (×-is-set (carrier-is-set G A) (carrier-is-set H B))
      , (λ x y w → ap2 _,_ (action-assoc G A (pr₁ x) (pr₁ y) (pr₁ w))
                           (action-assoc H B (pr₂ x) (pr₂ y) (pr₂ w)))
      , λ w → ap2 _,_ (action-unit G A  (pr₁ w))
                      (action-unit H B (pr₂ w)))

  _⊙_ : {G : Group 𝓤} → (A : Action' {𝓥 = 𝓥} G)
                       → (B : Action' {𝓥 = 𝓦} G) →
                       Action' {𝓥 = 𝓥 ⊔ 𝓦} G
  _⊙_ {G = G} A B
    = (⟨ A ⟩ × ⟨ B ⟩)
    , (λ g (a , b) → g ◂⟨ G ∣ A ⟩ a , g ◂⟨ G ∣ B ⟩ b)
    , ×-is-set (carrier-is-set G A) (carrier-is-set G B)
    , (λ g h (a , b) → ap2 _,_
        (action-assoc G A g h a)
        (action-assoc G B g h b))
    , λ (a , b) → ap2 _,_
        (action-unit G A a)
        (action-unit G B b)



  -- Every constant set has an indexed action:
  const-action : (G : Group 𝓤) → (A : Action' {𝓥 = 𝓥} G) →
    (⟨B⟩ : 𝓦 ̇) → is-set ⟨B⟩ → indexed-action G A
  const-action G A ⟨B⟩ ⟨B⟩set
    = (λ _ → ⟨B⟩)
    , (λ g b → b)
    , (λ a → ⟨B⟩set)
    , (λ g h b → NB: b since refl and refl)
    , λ b → NB: b since refl and refl


  commute : {X : 𝓦 ̇} → (g◃_ h⋖_ : X → X ) → 𝓦 ̇
  commute {X = X} g◂_ h⋖_ =
    (x : X) → g◂ (h⋖ x) ＝ h⋖ (g◂ x)

  instance
    ford : {X : 𝓥 ̇} {x : X} → x ＝ x
    ford {x} = refl

  action-structures-commute : (G : Group 𝓤) → (H : Group 𝓥) →
    {X : 𝓦 ̇} →
    (_◂_ : action-structure G X) →
    (_⋖_ : action-structure H X) →
    𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  action-structures-commute G H {X} _◂_ _⋖_ =
    (g : ⟨ G ⟩) → (h : ⟨ H ⟩) → commute (g ◂_) (h ⋖_)

  actions-commute : (G : Group 𝓤) → (H : Group 𝓥) →
    (A : Action' {𝓥 = 𝓦} G) →
    (B : Action' {𝓥 = 𝓦} H) →
    {{ ford : ⟨ A ⟩ ＝ ⟨ B ⟩ }} →
    𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  actions-commute G H A@( X , _◂_ , _)
                      B@(.X , _⋖_ , _)
                  {{ford = refl}}
    = action-structures-commute G H (_◂_) (_⋖_)


  merge : (G : Group 𝓤) → (A : Action' {𝓥 = 𝓦} G) →
          (H : Group 𝓥) → (B : Action' {𝓥 = 𝓦} H) →
          {{ford : ⟨ A ⟩ ＝ ⟨ B ⟩ }} →
          actions-commute G H A B →
          Action' {𝓥 = 𝓦} (G ⊗ H)
  merge G@(_ , _·_ , _) A@(X , _◂_ , _)
        H@(_ , _⊙_ , _) B@(.X , _⋖_ , _)
        {{ford = refl}}
        comm
    = X
    , (λ (g , h) x → g ◂ (h ⋖ x) )
    , carrier-is-set G A
    , (λ (g₁ , h₁) (g₂ , h₂) x →
        (g₁ · g₂) ◂ ((h₁ ⊙ h₂) ⋖ x)
        ＝⟨ ap ((g₁ · g₂) ◂_)
           (action-assoc H B h₁ h₂ x) ⟩
        (g₁ · g₂) ◂ (h₁ ⋖ (h₂ ⋖ x))
        ＝⟨ action-assoc G A g₁ g₂ (h₁ ⋖ (h₂ ⋖ x)) ⟩
        g₁ ◂ ( g₂ ◂ (h₁ ⋖ (h₂ ⋖ x)))
        ＝⟨ ap (g₁ ◂_)
            (comm g₂ h₁ (h₂ ⋖ x)) ⟩
        (g₁ ◂ (h₁ ⋖ (g₂ ◂ (h₂ ⋖ x)))) ∎)
    , λ x →
        (unit G ◂ (unit H ⋖ x) )
          ＝⟨ action-unit G A (unit H ⋖ x) ⟩
        unit H ⋖ x
          ＝⟨ action-unit H B x ⟩
        x ∎

\end{code}
