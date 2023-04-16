Andrew Sneap and Ohad Kammar

(Finally) define the reals taking advantage of symmetry


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
open import DedekindReals.Symmetry.ActionsConstructions
open import DedekindReals.Symmetry.Equivariance
open import DedekindReals.Symmetry.Transport
open import DedekindReals.Symmetry.S2

module DedekindReals.Symmetry.Reals.Type
 (pe : Prop-Ext)
 (pt : propositional-truncations-exist)
 (fe : Fun-Ext)
 {𝓤 : Universe} where

   open DedekindReals.Symmetry.UF.SurelyThisExistsSomewhere pe fe
   open import DedekindReals.Symmetry.MetaRelations pe pt fe
   open SetConstructions ℚ (ℚ-is-set fe)
   open import DedekindReals.Symmetry.Relations-S2 pe pt fe
   open SetConstructions-S2 ℚ (ℚ-is-set fe)
   open import DedekindReals.Type pe pt fe
   open PropositionalTruncation pt

   open import DedekindReals.Symmetry.Cuts pe pt fe ℚ (ℚ-is-set fe)

   ℚ<  ℚ> : 𝓟 (ℚ × ℚ)
   ℚ< (p , q)
     = p < q
     , ℚ<-is-prop p q
   ℚ> = opposite ℚ<

   pre-cut : 𝓤₁ ̇
   pre-cut =  𝓟 ℚ × 𝓟 ℚ

   left-rounded-wrt-ℚ<-rounded-left :
     (L : 𝓟 ℚ) →
       ⟨ left-rounded-wrt ℚ< L ⟩  →
       rounded-left L
   left-rounded-wrt-ℚ<-rounded-left L lrounded p
     = (λ ⟨Lp⟩ →
       ∥∥-induction
         (λ _ → ∃-is-prop)
         (λ { (q , p<q , Lq) → ∣ q , p<q , Lq ∣})
       (pr₁ (lrounded p) (⟨Lp⟩)))
     , ∥∥-induction
         (λ _ → holds-is-prop (L p))
         λ { (q , p<q , Lq) →
           (pr₂ (lrounded p)
             ∣ q , p<q , Lq ∣) }

   rounded-left-left-rounded-wrt-ℚ< :
     (L : 𝓟 ℚ) →
       rounded-left L →
       ⟨ left-rounded-wrt ℚ< L ⟩
   rounded-left-left-rounded-wrt-ℚ< L lrounded p
     = (λ Lp →
       ∥∥-induction
         (λ _ → ∃-is-prop)
         (λ {(q , p<q , Lq) → ∣ q , p<q , Lq ∣})
         (pr₁ (lrounded p) Lp))
     , ∥∥-induction
         (λ _ → holds-is-prop (L p))
         (λ { (q , p<q , Lq) →
         (pr₂ (lrounded p) ∣ q , p<q , Lq ∣)})
   -- Boilerplate galore...

   right-rounded-wrt-ℚ<-rounded-right :
     (R : 𝓟 ℚ) →
       ⟨ right-rounded-wrt ℚ< R ⟩  →
       rounded-right R
   right-rounded-wrt-ℚ<-rounded-right R rrounded p
     = (λ ⟨Rp⟩ →
       ∥∥-induction
         (λ _ → ∃-is-prop)
         (λ { (q , p>q , Rq) → ∣ q , p>q , Rq ∣})
         (pr₁ (rrounded p) ⟨Rp⟩))
     , ∥∥-induction
         (λ _ → holds-is-prop (R p))
         λ { (q , p>q , Rq) →
           (pr₂ (rrounded p)
             ∣ q , p>q , Rq ∣) }

   rounded-right-right-rounded-wrt-ℚ< :
     (R : 𝓟 ℚ) →
       rounded-right R →
       ⟨ right-rounded-wrt ℚ< R ⟩
   rounded-right-right-rounded-wrt-ℚ< R rrounded p
     = (λ Rp →
       ∥∥-induction
         (λ _ → ∃-is-prop)
         (λ {(q , p>q , Rq) → ∣ q , p>q , Rq ∣})
         (pr₁ (rrounded p) (Rp)))
     , ∥∥-induction
         (λ _ → (holds-is-prop (R p)))
         (λ { (q , p>q , Rq) →
         (pr₂ (rrounded p) ∣ q , p>q , Rq ∣)})


   -- separate out the S₂-symmetric parts of a cut
   semi-cut : 𝓟' (pre-cut)
   semi-cut (L , R) =
     (semi-cut-wrt ℚ< L) ∧Ω (semi-cut-wrt ℚ> R)

   -- TODO: refactor into a lift predicate into an internal
   -- predicate, and derive equivalence

   -- We can define disjoint and located precuts at the level of
   -- abstract cuts, but I don't have a good reason to do it

   disjoint-cut : 𝓟 (pre-cut)
   disjoint-cut (L , R)
     = Lift _ (disjoint L R)
     , lift-is-prop
       (disjoint-is-prop L R)

   disjoint-cut-disjoint : ((L , R) : pre-cut) →
     ⟨ disjoint-cut (L , R) ⟩ → disjoint L R
   disjoint-cut-disjoint (L , R) disj = lower disj

   disjoint-disjoint-cut : ((L , R) : pre-cut) →
     disjoint L R →
     ⟨ disjoint-cut (L , R) ⟩
   disjoint-disjoint-cut (L , R) disj = lift _ disj

   located-cut : 𝓟 (pre-cut)
   located-cut (L , R)
     = Lift _ (located L R)
     , lift-is-prop
       (located-is-prop L R)

   located-cut-located : ((L , R) : pre-cut) →
     ⟨ located-cut (L , R) ⟩ → located L R
   located-cut-located (L , R) loc = lower loc

   located-located-cut : ((L , R) : pre-cut) →
     located L R →
     ⟨ located-cut (L , R) ⟩
   located-located-cut (L , R) loc = lift _ loc

   is-cut : 𝓟 (pre-cut)
   is-cut = semi-cut ∧ (disjoint-cut ∧ located-cut)

   -- The point: thanks to our use of propositions, we can use a
   -- Σ-type instead of a truncation
   ℝ' : 𝓤₁ ̇
   ℝ' = Σ LR ꞉ pre-cut , ⟨ is-cut LR ⟩

   -- We'll shamelessly cannibalise Andrew's existing development
   -- As a consequence, we'll see how horrible it is to move
   -- from an internal language to an external one.
   -- Most of the horror has already happened when we defined
   -- each of the components
   is-cut-isCut : ((L , R) : pre-cut) → ⟨ is-cut (L , R) ⟩ →
     isCut L R
   is-cut-isCut LR@(L , R)
     (((L-rounded , L-inhabited)
      ,(R-rounded , R-inhabited))
     , LR-disjoint , LR-located)
     = inhabited-pred-inhabited L L-inhabited
     , inhabited-pred-inhabited R R-inhabited
     , left-rounded-wrt-ℚ<-rounded-left L L-rounded
     , right-rounded-wrt-ℚ<-rounded-right R R-rounded
     , disjoint-cut-disjoint (L , R) LR-disjoint
     , located-cut-located (L , R) LR-located

   isCut-is-cut : ((L , R) : pre-cut) →
     isCut L R →
     ⟨ is-cut (L , R) ⟩
   isCut-is-cut LR@(L , R)
     ( L-inhabited
     , R-inhabited
     , L-rounded
     , R-rounded
     , LR-disjoint
     , LR-located
     ) = ( ( rounded-left-left-rounded-wrt-ℚ< L L-rounded
           , inhabited-inhabited-pred L L-inhabited)
         , ( rounded-right-right-rounded-wrt-ℚ< R R-rounded
           , inhabited-inhabited-pred R R-inhabited))
       , disjoint-disjoint-cut LR LR-disjoint
       , located-located-cut LR LR-located

   ℝ'-is-set : is-set ℝ'
   ℝ'-is-set =
     sigma-is-set
       (×-is-set (𝓟-is-set' fe pe)
                 (𝓟-is-set' fe pe))
       λ cut → props-are-sets (holds-is-prop (is-cut cut))

   -- as a consequences:
   ℝ≃ℝ' : ℝ ≃ ℝ'
   ℝ≃ℝ' = (λ {(LR , isCutData) →
              LR , isCut-is-cut LR isCutData})
         , ( ℝ'→ℝ
           , λ x → to-subtype-＝ (holds-is-prop ∘ is-cut)
                                 refl)
         , ( ℝ'→ℝ
           , λ x → to-subtype-＝
               (λ (L , R) → isCut-is-prop L R)
               refl
           )
     where
       ℝ'→ℝ : ℝ' → ℝ
       ℝ'→ℝ (LR , is-cut-data) =
         LR , is-cut-isCut LR is-cut-data

   instance
     canonical-map-ℝ-to-ℝ' : Canonical-Map ℝ ℝ'
     ι {{canonical-map-ℝ-to-ℝ'}} = ⌜ ℝ≃ℝ' ⌝

   instance
     canonical-map-ℝ'-to-ℝ : Canonical-Map ℝ' ℝ
     ι {{canonical-map-ℝ'-to-ℝ}} = ⌜ ℝ≃ℝ' ⌝⁻¹

   instance
     canonical-map-ℚ-to-ℝ' : Canonical-Map ℚ ℝ'
     ι {{canonical-map-ℚ-to-ℝ'}} x = ι {X = ℝ} (ι x)

\end{code}
