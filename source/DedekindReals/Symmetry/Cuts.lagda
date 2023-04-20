Andrew Sneap and Ohad Kammar

Define cuts abstractly w.r.t. to any set (to make use of symmetry)

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
open import DedekindReals.Symmetry.S2

module DedekindReals.Symmetry.Cuts
 (pe : Prop-Ext)
 (pt : propositional-truncations-exist)
 (fe : Fun-Ext)
 {𝓤 : Universe}
 (X : 𝓤 ̇) (Xset : is-set X)
  where
     open DedekindReals.Symmetry.UF.SurelyThisExistsSomewhere pe fe
     open import DedekindReals.Symmetry.MetaRelations pe pt fe
     open SetConstructions X Xset
     open import DedekindReals.Symmetry.Relations-S2 pe pt fe
     open SetConstructions-S2 X Xset
     open GroupConstructions
     open import DedekindReals.Symmetry.S2
     open import DedekindReals.Type pe pt fe
     open PropositionalTruncation pt
     open import DedekindReals.Symmetry.Transport pe fe

     pre-cut-wrt : (_<_ : Rel) → 𝓤 ⁺ ̇
     pre-cut-wrt _ = 𝓟 X × 𝓟 X

     pre-cut-is-set : (_<_ : Rel) → is-set (pre-cut-wrt _<_)
     pre-cut-is-set _<_ = ×-is-set (𝓟-is-set' fe pe)
                                   (𝓟-is-set' fe pe)

     rounded-wrt : (R : Rel) → 𝓟' {𝓥 = 𝓤} (𝓟 X)
     rounded-wrt R P = (c𝓟∋Pi X
           (P ⟺ s𝓟∋Sigma X ((R ∧ (P ∘ pr₂ ))) ))

     left-rounded-wrt : (R : Rel) → 𝓟' (𝓟' X)
     left-rounded-wrt R = rounded-wrt R

     right-rounded-wrt : (R : Rel) → 𝓟' (𝓟' X)
     right-rounded-wrt R =
       left-rounded-wrt (opposite R)

     inhabited-pred : 𝓟' (𝓟 X)
     inhabited-pred P = c𝓟∋Sigma X P

     inhabited-pred-inhabited : (P : 𝓟' X) →
       ⟨ inhabited-pred P ⟩ → inhabited P
     inhabited-pred-inhabited P
       = ∥∥-induction
         (λ _ →
           inhabited-subsets.being-inhabited-is-prop pt P)
         λ { (p , Pp) → ∣ p , Pp ∣}

     inhabited-inhabited-pred : (P : 𝓟' X) →
       inhabited P → ⟨ inhabited-pred P ⟩
     inhabited-inhabited-pred P = ∥∥-induction
       (λ _ → holds-is-prop (inhabited-pred P))
       λ { (p , Pp) → ∣ p , (Pp) ∣ }

     semi-cut-wrt : (R : Rel) → 𝓟' (𝓟' X)
     semi-cut-wrt R = rounded-wrt R ∧ inhabited-pred
