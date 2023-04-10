Andrew Sneap and Ohad Kammar

The views that will eventually do the work. Still largely
experimental, hopefully will clarify once we work out some examples

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

module DedekindReals.Symmetry.Views where

-- The workhorse: promoting the group inversion and action to relations

-- Convention: group elements are always inside brackets

data [⟨_⟩]⟨[_]＝[_]⟩ (G : Group 𝓤) : ⟨ G ⟩ → ⟨ G ⟩ → 𝓤 ̇ where
  invert : (g : ⟨ G ⟩) → [⟨ G ⟩]⟨[ g ]＝[ inv G g ]⟩

data [⟨_∣_⟩]⟨[_]◂_＝[_]◂_⟩
  (G : Group 𝓤) (A : Action G) : ⟨ G ⟩ → ⟨ A ⟩ → ⟨ G ⟩ → ⟨ A ⟩ → 𝓤 ̇ where
  check : {g : ⟨ G ⟩} → {a : ⟨ A ⟩} → {h : ⟨ G ⟩} → {b : ⟨ A ⟩} →
    g ◂⟨ G ∣ A ⟩ a ＝ h ◂⟨ G ∣ A ⟩ b
    →
    [⟨ G ∣ A ⟩]⟨[ g ]◂ a ＝[ h ]◂ b ⟩

-- This view lets us invert the action:
data [⟨_∣_⟩]⟨[1]◂_＝[*]◂*⟩
  (G : Group 𝓤) (A : Action G) : ⟨ A ⟩ → 𝓤 ̇ where
  invert' : (g : ⟨ G ⟩) → (a : ⟨ A ⟩) →
    [⟨ G ∣ A ⟩]⟨[1]◂ g ◂⟨ G ∣ A ⟩ a ＝[*]◂*⟩

[⟨_∣_⟩]⟨[_]◂_＝[?]◂?⟩ : (G : Group 𝓤) (A : Action G) → (g : ⟨ G ⟩) → (a : ⟨ A ⟩) →
  [⟨ G ∣ A ⟩]⟨[1]◂ a ＝[*]◂*⟩
[⟨ G ∣ A ⟩]⟨[ g ]◂ a ＝[?]◂?⟩ =
  transport  [⟨ G ∣ A ⟩]⟨[1]◂_＝[*]◂*⟩
  (inv-act-inverse-left G A g a)
  (invert' {G = G} {A = A} (inv G g) (g ◂⟨ G ∣ A ⟩ a))

{-
[⟨_⟩]⟨[_]⟩⁻¹ : (G : Group 𝓤) → {g h : ⟨ G ⟩} →
  [⟨ G ⟩]⟨[ g ]↔[ h ]⟩ →
  [⟨ G ⟩]⟨[ h ]↔[ g ]⟩
[⟨ G ⟩]⟨[ invert r ]⟩⁻¹ = transport [⟨ G ⟩]⟨[ inv G r ]↔[_]⟩
  (inv-involutive G r)
  (invert (inv G r))

-- Now we can define some partial views

data [⟨_∣_⟩]⟨_[*]↔[_]*⟩ (G : Group 𝓤) (A : Action G)
  : (a : ⟨ A ⟩) → (x : ⟨ G ⟩) → 𝓤 ̇ where
  ⟨[_]↔[]_⟩ : (h : ⟨ G ⟩ ) → (a : ⟨ A ⟩) →
    [⟨ G ∣ A ⟩]⟨ inv G h ◂⟨ G ∣ A ⟩ a [*]↔[ h ]*⟩

data [⟨_∣_⟩]⟨*[*]↔[_]_⟩ (G : Group 𝓤) (A : Action G)
  : (x : ⟨ G ⟩) → (a : ⟨ A ⟩) → 𝓤 ̇ where
  ⟨_[_]↔[]⟩ : (h : ⟨ G ⟩ ) → (a : ⟨ A ⟩) →
    [⟨ G ∣ A ⟩]⟨*[*]↔[ h ] a ⟩


[⟨_⟩]⟨←[_]⟩ : (G : Group 𝓤) → (g : ⟨ G ⟩) → [⟨ G ⟩]⟨[ inv G g ]↔[ g ]⟩
[⟨ G ⟩]⟨←[ g ]⟩ = [⟨ G ⟩]⟨[ invert g ]⟩⁻¹

[⟨_⟩]⟨*←[_]⟩ : (G : Group 𝓤) → (g : ⟨ G ⟩) → Σ [⟨ G ⟩]⟨[_]↔[ g ]⟩
[⟨ G ⟩]⟨*←[ g ]⟩ = inv G g , [⟨ G ⟩]⟨←[ g ]⟩

[⟨_∣_⟩]⟨_[]↔[_]⟩ : (G : Group 𝓤) (A : Action G) (a : ⟨ A ⟩) (g : ⟨ G ⟩) →
  [⟨ G ∣ A ⟩]⟨ a [*]↔[ g ]*⟩
[⟨ G ∣ A ⟩]⟨ a []↔[ g ]⟩ with [⟨ G ⟩]⟨*←[ g ]⟩
[⟨ G ∣ A ⟩]⟨ a []↔[ .(inv G h) ]⟩ | h , invert .h = transport
  [⟨ G ∣ A ⟩]⟨_[*]↔[ inv G h ]*⟩
  (inv-act-inverse-left G A (inv G h) a)
  (⟨[ inv G h ]↔[] inv G h ◂⟨ G ∣ A ⟩ a ⟩)

[⟨_∣_⟩]⟨[]↔[_]_⟩ : (G : Group 𝓤) (A : Action G) (g : ⟨ G ⟩) (a : ⟨ A ⟩) →
  [⟨ G ∣ A ⟩]⟨*[*]↔[ g ] a ⟩
[⟨ G ∣ A ⟩]⟨[]↔[ g ] a ⟩ = ⟨ {!inv G g ◂⟨ G ∣ A ⟩ a!} [ {!!} ]↔[]⟩


[⟨_∣_⟩]⟨_⟩⁻¹ : (G : Group 𝓤) → (A : Action G) → {g h : ⟨ G ⟩} → {a b : ⟨ A ⟩} →
  [⟨ G ∣ A ⟩]⟨ a [ g ]↔[ h ] b ⟩ →
  [⟨ G ∣ A ⟩]⟨ b [ h ]↔[ g ] a ⟩

[⟨_∣_⟩]⟨_⟩⁻¹ G A {g} {.(inv G g)} {a} {.(action-op-syntax G A g a)} (act .g .a)
  with [⟨ G ⟩]⟨*←[ g ]⟩
[⟨_∣_⟩]⟨_⟩⁻¹ G A {.(inv G x)} {.(inv G (inv G x))} {a} {.(action-op-syntax G A (inv G x) a)} (act .(inv G x) .a) | x , invert .x =
  transport2 ([⟨ G ∣ A ⟩]⟨ inv G x ◂⟨ G ∣ A ⟩ a  [_]↔[ inv G x ]_⟩)
    ((inv-involutive G x)⁻¹)
    (inv-act-inverse-right G A x a)
    (act x (inv G x ◂⟨ G ∣ A ⟩ a))

[⟨_∣_⟩]⟨[_]←_⟩ : (G : Group 𝓤) → (A : Action G) → (g : ⟨ G ⟩) → (a : ⟨ A ⟩) →
  [⟨ G ∣ A ⟩]⟨ (inv G g ◂⟨ G ∣ A ⟩ a) [ g ]↔[ inv G g ] a ⟩
[⟨ G ∣ A ⟩]⟨[ g ]← a ⟩ = [⟨ G ∣ A ⟩]⟨ transport
  [⟨ G ∣ A ⟩]⟨ a [ inv G g ]↔[_] inv G g ◂⟨ G ∣ A ⟩ a ⟩
  (inv-involutive G g)
  (act (inv G g) a) ⟩⁻¹

[⟨_∣_⟩]⟨←[_]_⟩ : (G : Group 𝓤) → (A : Action G) → (g : ⟨ G ⟩) → (a : ⟨ A ⟩) →
  [⟨ G ∣ A ⟩]⟨ (g ◂⟨ G ∣ A ⟩ a) [ inv G g ]↔[ g ] a ⟩
[⟨ G ∣ A ⟩]⟨←[ g ] a ⟩ = [⟨ G ∣ A ⟩]⟨ act g a ⟩⁻¹

----------------------------

{- not sure I need these
[⟨_∣_⟩]⟨_[]→[_]⟩ : (G : Group 𝓤) → (A : Action G) → (a : ⟨ A ⟩) → (g : ⟨ G ⟩) →
  [⟨ G ∣ A ⟩]⟨ a [ inv G g ]↔[ h ] b ⟩ ➙
  [⟨ G ∣ A ⟩]⟨ g ◂⟨ G ∣ A ⟩ a [ g ]↔[  ] g ◂⟨ G ∣ A ⟩ a ⟩

[⟨_∣_⟩]⟨_[]↔[_]⟩ : (G : Group 𝓤) → (A : Action G) → (a : ⟨ A ⟩) → (g : ⟨ G ⟩) →
  [⟨ G ∣ A ⟩]⟨ a [ inv G g ]↔[ g ] g ◂⟨ G ∣ A ⟩ a ⟩
[⟨ G ∣ A ⟩]⟨ a []↔[ g ]⟩ with [⟨ G ⟩]⟨*←[ g ]⟩
[⟨ G ∣ A ⟩]⟨ a []↔[ .(inv G r) ]⟩ | r , invert .r = {![⟨ G ⟩]⟨[ ? ]⟩⁻¹!}
-}
-}

{-
[⟨_∣_⟩]⟨*[*]←[_]_⟩ : (G : Group 𝓤) → (A : Action G) → (g : ⟨ G ⟩) → (a : ⟨ A ⟩) →
  ΣΣ [⟨ G ∣ A ⟩]⟨_[_]↔[ g ] a ⟩
[⟨ G ∣ A ⟩]⟨*[*]←[ g ] a ⟩ = _ , _ , [⟨ G ∣ A ⟩]⟨←[ g ] a ⟩

[⟨_∣_⟩]⟨[*]←[_]_⟩ : (G : Group 𝓤) → (A : Action G)  →
  (g : ⟨ G ⟩) → (a : ⟨ A ⟩) →
  Σ [⟨ G ∣ A ⟩]⟨ (g ◂⟨ G ∣ A ⟩ a) [_]↔[ g ] a ⟩
[⟨ G ∣ A ⟩]⟨[*]←[ g ] a ⟩ =  _ , [⟨ G ∣ A ⟩]⟨←[ g ] a ⟩

[⟨_∣_⟩]⟨*←[_]_⟩ : (G : Group 𝓤) → (A : Action G)  →
  (g : ⟨ G ⟩) → (a : ⟨ A ⟩) →
  Σ [⟨ G ∣ A ⟩]⟨_[ inv G g ]↔[ g ] a ⟩
[⟨ G ∣ A ⟩]⟨*←[ g ] a ⟩ =  _ , [⟨ G ∣ A ⟩]⟨←[ g ] a ⟩

--     r h     r.h
[⟨_∣_⟩]⟨_[*]←[_]*⟩ : (G : Group 𝓤) → (A : Action G)  →
  (a : ⟨ A ⟩) → (g : ⟨ G ⟩) →
  ΣΣ [⟨ G ∣ A ⟩]⟨ a [_]↔[ g ]_⟩

[⟨_∣_⟩]⟨_[_]→[*]*⟩ : (G : Group 𝓤) → (A : Action G)  →
  (a : ⟨ A ⟩) → (g : ⟨ G ⟩) →
  ΣΣ [⟨ G ∣ A ⟩]⟨ a [ g ]↔[_]_⟩


[⟨ G ∣ A ⟩]⟨ a [*]←[ g ]*⟩ with [⟨ G ⟩]⟨*←[ g ]⟩
[⟨ G ∣ A ⟩]⟨ a [*]←[ .(inv G r) ]*⟩ | r , invert .r = _ , _ , act r a

[⟨_∣_⟩]⟨_[_]↔[*]*⟩ : (G : Group 𝓤) → (A : Action G) →
  (a : ⟨ A ⟩ ) →
           (g : ⟨ G ⟩) →
         ΣΣ [⟨ G ∣ A ⟩]⟨ a [ g ]↔[_]_⟩
[⟨ G ∣ A ⟩]⟨ a [ g ]↔[*]*⟩ = {!!}


-}

open DedekindReals.Symmetry.UF.SurelyThisExistsSomewhere
  public hiding (_⟺_)

return-fun : (G : Group 𝓤) → (A : Action G) →
           ((⟨B⟩ , foo) : ⟨ G ∣ A ⟩-indexed-action) → (a : ⟨ A ⟩ ) →
           (g : ⟨ G ⟩) →
           (⟨B⟩ (g ◂⟨ G ∣ A ⟩ a) → ⟨B⟩ a)
return-fun G A B a g result = {!!} {-with [⟨ G ∣ A ⟩]⟨ g ◂⟨ G ∣ A ⟩ a []↔[ g ]⟩
return-fun G A B a g result | foo = {!foo!}

return-fun G A B@(⟨B⟩ , _) .(h ◂⟨ G ∣ A ⟩ x) .(inv G h) result | take h x
    = transport ⟨B⟩ (inv-act-inverse-right G A h _) (h ◃⟨ G ∣ A ∣ B ⟩ result)

-}
{-
  --- I think this is subsumed
  invert-inv-action : {g : _} {x y : _} → y ~[[ inv G g ]]~ x → x ~[[ g ]]~ y
  invert-inv-action {g} {x} {y} view =
    transport (λ h → x ~[[ h ]]~ y)
    (inv-involutive g)
    (invert-action view)

  ekat : (g : ⟨ G ⟩) → (a : ⟨ A ⟩) → a ~[ g ]~*
  ekat g a = transport2 (λ x h → x ~[ h ]~*)
    (inv-act-inverse-left g a)
    (inv-involutive g)
    (take (inv G g) (g ◂⟨ G ∣ A ⟩ a))




out-log : (G : Group 𝓤) → (A : Action G) →
          ((⟨B⟩ , foo) : ⟨ G ∣ A ⟩-indexed-action) → (a : ⟨ A ⟩ ) →
          (g : ⟨ G ⟩) →
          (a ~[ g ]~*)
          × (⟨B⟩ (g ◂⟨ G ∣ A ⟩ a) → ⟨B⟩ a)
out-log G A B a g = ekat G A g a , return-fun G A B a g

-}


\end{code}
