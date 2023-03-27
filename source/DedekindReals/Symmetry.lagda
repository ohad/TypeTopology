Andrew Sneap and Ohad Kammar

\paragraph{Summary.}  Dealing with multiplication involves a
\emph{lot} of case analyses. Here we try to use \emph{symmetric
programming} techniques to manage this complexity. As a
proof-of-concept, we prove that $u\cdot v$ is disjoint, which I
believe was challenging.

We'll be mostly following the structure of
DedekindReals.Multiplication, copy/pasted, refactoring pending.

\begin{code}
--{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.Order
open import UF.PropTrunc
open import MLTT.Sigma
open import Notation.General

open import UF.Subsingletons
open import UF.FunExt
open import UF.Powerset

open import Rationals.Type
open import Rationals.Order

open import Groups.Type
open import Groups.GroupActions
\end{code}

\section{Symmetric Programming}

By symmetric programming, I mean a handful of programming constructs
that let us program/prove a larger number of symmetric cases by only
considering a representative from each orbit. Since this is a new
style of dependently-typed programming, there is going to be a gap
between how we'd like to express those constructs, and how we can
express them in Agda without having to deal with the internals of the type-checker.

\begin{code}
module DedekindReals.Symmetry where

inv-involutive : (G : Group 𝓤) → (g : ⟨ G ⟩) → inv G (inv G g) ＝ g
inv-involutive g = {!!} -- fun to be had here

data _≈_ {X : 𝓤 ̇} (x : X) : {Y : 𝓤 ̇} → (y : Y) → 𝓤 ⁺ ̇
    where
    NB:_since_and_ : forall {Y} (y : Y) →
      (prf : X ＝ Y) → transport id prf x ＝ y → x ≈ y


module SymmetricProgramming (G : Group 𝓤) (A : Action G) where
  -- heterogeneous equality

  indexed-action-structure-over : (⟨B⟩ : ⟨ A ⟩ → 𝓤 ̇) → 𝓤 ̇
  indexed-action-structure-over ⟨B⟩ =
    (g : ⟨ G ⟩) → {x : ⟨ A ⟩} → ⟨B⟩ x → ⟨B⟩ (g ◂⟨ G ∣ A ⟩ x)

  indexed-action-axioms : (⟨B⟩ : ⟨ A ⟩ → 𝓤 ̇) →
    indexed-action-structure-over ⟨B⟩ → 𝓤 ⁺ ̇
  indexed-action-axioms ⟨B⟩ _·_ =
      ((a : ⟨ A ⟩) → is-set (⟨B⟩ a))
    × ((g h : ⟨ G ⟩){a : ⟨ A ⟩}(b : ⟨B⟩ a) →
        ((g ·⟨ G ⟩ h) · b) ≈ (g · (g · b))  )
    × ({a : ⟨ A ⟩} → (b : ⟨B⟩ a) → (unit G · b) ≈ b)

  indexed-action-over : (⟨B⟩ : ⟨ A ⟩ → 𝓤 ̇) → 𝓤 ⁺ ̇
  indexed-action-over ⟨B⟩ = Σ (indexed-action-axioms ⟨B⟩)

  indexed-action : 𝓤 ⁺ ̇
  indexed-action = Σ indexed-action-over

  indexed-action-op : ((⟨B⟩ , structure) : indexed-action) →
    indexed-action-structure-over ⟨B⟩
  indexed-action-op (⟨B⟩ , _◃⟨B⟩_ , axioms) = _◃⟨B⟩_

  -- The point: an indexed action is an action on the Σ-type that
  -- lives over A

  as-action : {⟨B⟩ : ⟨ A ⟩ → 𝓤 ̇ } →
    indexed-action-over ⟨B⟩ → Action-structure G (Σ ⟨B⟩)
  as-action (_·_ , axioms)
    = (λ g → λ { (a , b) → (g ◂⟨ G ∣ A ⟩ a)  , (g · b)})
    , {!!} -- lots of HoTT fun to be had here

  inv-act-inverse-left : (g : ⟨ G ⟩) → (a : ⟨ A ⟩) →
    (inv G g) ◂⟨ G ∣ A ⟩ (g ◂⟨ G ∣ A ⟩ a) ＝ a
  inv-act-inverse-left g a =
     ((g ⁱⁿᵛ) · (g · a)    ＝⟨ action-assoc G A (g ⁱⁿᵛ) g a  ⁻¹ ⟩
     ((g ⁱⁿᵛ) ·⟨ G ⟩ g) · a ＝⟨ ap (_· a) (inv-left G g) ⟩
     (unit G) · a          ＝⟨ action-unit G A a ⟩
     a ∎)
    where _ⁱⁿᵛ : ⟨ G ⟩ → ⟨ G ⟩
          _ⁱⁿᵛ = inv G
          _·_ : ⟨ G ⟩ → ⟨ A ⟩ → ⟨ A ⟩
          _·_ = action-op G A

  inv-act-inverse-right : (g : ⟨ G ⟩) → (a : ⟨ A ⟩) →
    g ◂⟨ G ∣ A ⟩ ((inv G g) ◂⟨ G ∣ A ⟩ a) ＝ a
  inv-act-inverse-right g a = {!!} -- fun to be had here

open SymmetricProgramming public

transport2 : {X Y : 𝓤 ̇ } (A : X → Y → 𝓥 ̇ ) {x1 x2 : X} {y1 y2 : Y}
          → x1 ＝ x2 → y1 ＝ y2 → A x1 y1 → A x2 y2
transport2 A refl refl x = x

ap2 : {X Y : 𝓤 ̇ } {Z : 𝓥 ̇} (f : X → Y → Z ) {x1 x2 : X} {y1 y2 : Y}
          → x1 ＝ x2 → y1 ＝ y2 → f x1 y1 ＝ f x2 y2
ap2 f refl refl = refl


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

ΣΣ : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇} {Y : 𝓥 ̇} → (Z : X → Y → 𝓦 ̇) →
  𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
ΣΣ Z = Σ (λ x → Σ (λ y → Z x y))

ΣΣΣ : {𝓤 𝓥 𝓦 𝓡 : Universe} {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} →
  (R : X → Y → Z → 𝓡 ̇) →
  𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓡 ̇
ΣΣΣ R = Σ (λ x → Σ (λ y → Σ (λ z → R x y z)))
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
⟨_∣_⟩-indexed-action : (G : Group 𝓤) → (A : Action G) → 𝓤 ⁺ ̇
⟨ A ∣ G ⟩-indexed-action = Σ (indexed-action-over A G)

⟨_⟩-indexed-action : {G : Group 𝓤} → (A : Action G) → 𝓤 ⁺ ̇
⟨_⟩-indexed-action {G = G} A = ⟨ G ∣ A ⟩-indexed-action

indexed-action-op-syntax : (G : Group 𝓤) (A : Action G) →
    ((⟨B⟩ , rest) : ⟨ G ∣ A ⟩-indexed-action) →
    indexed-action-structure-over G A  ⟨B⟩
indexed-action-op-syntax {𝓤} G A B = indexed-action-op G A B
syntax indexed-action-op-syntax G A B g y = g ◃⟨ G ∣ A ∣ B ⟩ y

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

module GenericActions {𝓤 : Universe} where

  data ⟨S₂⟩ : 𝓤 ̇  where
    id∈S₂  flip : ⟨S₂⟩

  _﹔_ : (x y : ⟨S₂⟩) → ⟨S₂⟩
  id∈S₂ ﹔ y = y
  flip ﹔ id∈S₂ = flip
  flip ﹔ flip = id∈S₂

  assoc-﹔ : associative _﹔_
  assoc-﹔ id∈S₂ id∈S₂ z = refl
  assoc-﹔ id∈S₂ flip id∈S₂ = refl
  assoc-﹔ id∈S₂ flip flip = refl
  assoc-﹔ flip id∈S₂ id∈S₂ = refl
  assoc-﹔ flip id∈S₂ flip = refl
  assoc-﹔ flip flip id∈S₂ = refl
  assoc-﹔ flip flip flip = refl

  left-neutral-﹔ : left-neutral id∈S₂ _﹔_
  left-neutral-﹔ x = refl

  right-neutral-﹔ : right-neutral id∈S₂ _﹔_
  right-neutral-﹔ id∈S₂ = refl
  right-neutral-﹔ flip = refl

  inv-S₂ : ⟨S₂⟩ → ⟨S₂⟩
  inv-S₂ x = x

  inv-left-﹔ : (x : ⟨S₂⟩) → (inv-S₂ x) ﹔ x ＝ id∈S₂
  inv-left-﹔ id∈S₂ = refl
  inv-left-﹔ flip = refl

  inv-right-﹔ : (x : ⟨S₂⟩) → x ﹔ (inv-S₂ x)  ＝ id∈S₂
  inv-right-﹔ id∈S₂ = refl
  inv-right-﹔ flip = refl


  S₂ : Group (𝓤)
  S₂ = ⟨S₂⟩ , (_﹔_
            , (λ {refl refl → refl})
            , (assoc-﹔
            , (id∈S₂
            , left-neutral-﹔
            , right-neutral-﹔
            , λ x → inv-S₂ x
                  , inv-left-﹔ x
                  , inv-right-﹔ x
                  )))

  _◂⟨S₂∣_²⟩_ : (π : ⟨S₂⟩) → (a : 𝓤 ̇) → a × a → a × a
  id∈S₂ ◂⟨S₂∣ a ²⟩ xy = xy
  flip  ◂⟨S₂∣ a ²⟩ (x , y) = y , x

  assoc-⟨S₂∣_²⟩ : (a : 𝓤 ̇) → is-assoc S₂ _◂⟨S₂∣ a ²⟩_
  assoc-⟨S₂∣ a ²⟩ id∈S₂ h x = refl
  assoc-⟨S₂∣ a ²⟩ flip id∈S₂ x = refl
  assoc-⟨S₂∣ a ²⟩ flip flip x = refl

  unital-⟨S₂∣_²⟩ : (a : 𝓤 ̇) → is-unital S₂ _◂⟨S₂∣ a ²⟩_
  unital-⟨S₂∣ a ²⟩ x = refl

  Flip : (a : 𝓤 ̇) → (is-set a) → Action S₂
  Flip a aSet = (a × a) , (_◂⟨S₂∣ a ²⟩_)
         , ×-is-set aSet aSet
         , assoc-⟨S₂∣ a ²⟩
         , unital-⟨S₂∣ a ²⟩

  ptwise : {X Y Z U V W : 𝓤 ̇} → (X → Y → Z) → (U → V → W) → (X × U → Y × V → Z × W)
  ptwise f g (x , u) (y , v) = (f x y) , (g u v)

  ptwise-group-structure : (G H : Group 𝓤) → group-structure (⟨ G ⟩ × ⟨ H ⟩)
  ptwise-group-structure G H  = ptwise (multiplication G) (multiplication H)

  assoc-ptwise : (G H : Group 𝓤) →  associative (ptwise-group-structure G H)
  assoc-ptwise G H x y z = ap2 _,_ (assoc G (pr₁ x) (pr₁ y) (pr₁ z))
                                   (assoc H (pr₂ x) (pr₂ y) (pr₂ z))
  left-neutral-ptwise : (G H : Group 𝓤) →
    left-neutral (unit G , unit H) (ptwise-group-structure G H)
  left-neutral-ptwise G H x = ap2 _,_ (unit-left G (pr₁ x))
                                      (unit-left H (pr₂ x))

  right-neutral-ptwise : (G H : Group 𝓤) →
    right-neutral (unit G , unit H) (ptwise-group-structure G H)
  right-neutral-ptwise G H x = ap2 _,_ (unit-right G (pr₁ x))
                                       (unit-right H (pr₂ x))
  _⊗_ : (G H : Group 𝓤) → Group 𝓤
  G ⊗ H = (⟨ G ⟩ × ⟨ H ⟩) , (ptwise-group-structure G H
        , ×-is-set (group-is-set G) (group-is-set H)
        , (assoc-ptwise G H
        , ((unit G , unit H)
        , (left-neutral-ptwise G H
        , (right-neutral-ptwise G H
        , (λ {x → (inv G (pr₁ x) , inv H (pr₂ x))
               , ((ap2 _,_ (inv-left G (pr₁ x)) (inv-left H (pr₂ x)))
               ,  (ap2 _,_ (inv-right G (pr₁ x)) (inv-right H (pr₂ x))))}))))))

  ∣_×_ : {G H : Group 𝓤} → (A : Action G) → (B : Action H) →
    Action (G ⊗ H)
  ∣_×_ {G} {H} A B
    = (⟨ A ⟩ × ⟨ B ⟩)
      , ((ptwise (action-op G A) (action-op H B))
      , (×-is-set (carrier-is-set G A) (carrier-is-set H B))
      , (λ x y w → ap2 _,_ (action-assoc G A (pr₁ x) (pr₁ y) (pr₁ w))
                           (action-assoc H B (pr₂ x) (pr₂ y) (pr₂ w)))
      , λ w → ap2 _,_ (action-unit G A  (pr₁ w))
                      (action-unit H B (pr₂ w)))

  -- Every constant set has an indexed action:
  const-action : (G : Group 𝓤) → (A : Action G) →
    (⟨B⟩ : 𝓤 ̇) → is-set ⟨B⟩ → indexed-action G A
  const-action G A ⟨B⟩ ⟨B⟩set
    = (λ _ → ⟨B⟩)
    , (λ g b → b)
    , (λ a → ⟨B⟩set)
    , (λ g h b → NB: b since refl and refl)
    , λ b → NB: b since refl and refl

  is-dep-equivariant : (G : Group 𝓤) → (A : Action G) →
    ((⟨B⟩ , structure) : ⟨ G ∣ A ⟩-indexed-action) →
    (f : (a : ⟨ A ⟩) → ⟨B⟩ a) → 𝓤 ⁺ ̇
  is-dep-equivariant G A B f
    = (g : ⟨ G ⟩ ) → (a : ⟨ A ⟩) →
    (f (g ◂⟨ G ∣ A ⟩ a)) ≈ (g ◃⟨ G ∣ A ∣ B ⟩ (f a))

  invariant : (G : Group 𝓤) → (A : Action G) →
    (⟨B⟩ : 𝓤 ̇) → is-set ⟨B⟩ →
    (f : ⟨ A ⟩ → ⟨B⟩) → 𝓤 ⁺ ̇
  invariant G A ⟨B⟩ ⟨B⟩set f =
    is-dep-equivariant G A (const-action G A ⟨B⟩ ⟨B⟩set) f

open GenericActions public

module Multiplication
         (pe : Prop-Ext)
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
         (nfe : ∀ {𝓤 𝓥} → DN-funext 𝓤 𝓥)
       where

   open import Rationals.Multiplication renaming (_*_ to _ℚ*_)
   open import Rationals.MinMax fe
   open import DedekindReals.Type pe pt fe
   open PropositionalTruncation pt

   _⇒_ : {X : 𝓤 ̇} → (x y : 𝓟 X) →  𝓟 X
   U ⇒ V = λ x → (⟨ U x ⟩ → ⟨ V x ⟩) , λ a b → nfe (λ u → {!pr₂ V!})


   -- Just an example --- I don't have a good feel for how teverything
   -- is set-up with dedekind cuts
   module Relations (X : 𝓤₀ ̇) (Xset : is-set X) where
     PreRel : 𝓤₀ ⁺ ̇
     PreRel = X × X → 𝓤₀ ̇

     pointwise-prop : PreRel → 𝓤₀ ̇
     pointwise-prop R = (x y : X) → is-prop (R (x , y))

     Rel : 𝓤₀ ⁺ ̇
     Rel = Σ pointwise-prop

     opposite : Rel → Rel
     opposite (⟨R⟩ , props) =
       (λ xy → ⟨R⟩ (flip ◂⟨ S₂ ∣ Flip X Xset  ⟩ xy))
       , λ x y x=₁y x=₂y → props y x x=₁y x=₂y

     _◂⟨S₂∣Rel⟩_ : action-structure S₂ Rel
     id∈S₂ ◂⟨S₂∣Rel⟩ R = R
     flip  ◂⟨S₂∣Rel⟩ R = opposite R

     assoc-Rel : is-assoc S₂ _◂⟨S₂∣Rel⟩_
     assoc-Rel id∈S₂ h x = refl
     assoc-Rel flip id∈S₂ x = refl
     assoc-Rel flip flip x = refl

     unital-Rel : is-unital S₂ _◂⟨S₂∣Rel⟩_
     unital-Rel x = refl

     RelIsSet : is-set Rel
     RelIsSet = {!-- should be able to set things up so this is true!}
     universeIsSet : is-set (𝓤₀ ̇)
     universeIsSet = {!-- This definitely isn't true, need to rethink the set-up!}

     S₂onRel : Action-structure S₂ Rel
     S₂onRel = _◂⟨S₂∣Rel⟩_
             , RelIsSet
             , assoc-Rel
             , unital-Rel

     S₂∣Rel : Action (S₂ {𝓤 = 𝓤₀ ⁺})
     S₂∣Rel = Rel , S₂onRel


     transitive-rel : 𝓟 Rel
     transitive-rel (⟨R⟩ , rel) =
       {!!} --(x y z : X) → ⟨R⟩ (x , y) → ⟨R⟩ (y , z) → ⟨R⟩ (x , z)

{-

     invariant-transitive :
       (R : Rel) →
       invariant S₂ S₂∣Rel (𝓤₀ ̇) universeIsSet
         transitive-rel
     invariant-transitive R id∈S₂ a
       = NB: (transitive-rel a) since refl and refl
     invariant-transitive R@(⟨R⟩ , struct) flip a
       = NB: {!-- I think this goes here
         flip ◃⟨ S₂ {𝓤 = 𝓤₀ ⁺}  ∣ S₂∣Rel ∣ const-action S₂ S₂∣Rel (𝓤₀ ̇) universeIsSet ⟩ transitive-rel a!}
           since refl and
         {!-- some HoTT fun. We ought to be able to postulate that
          -- transitivity is a proposition, and then show that a relation is transitive iff its opposite is transitive !}
-}
   pre-cut : 𝓤₁ ̇
   pre-cut =  𝓟 ℚ × 𝓟 ℚ



   \end{code}

   Multiplication is defined as in the HoTT Book. It reminds of interval multiplication of rational numbers.

   Inhabitedness: by inhabitedness of x and y, we find values
     on both sides of each. Then using the property that rationals have no
   least element, then using the relevant min/max calculation we
   trivially find a p which inhabits each cut of the product.

   Roundedness: roundedness in the left to right direction follows
   directly from density of rationals, and transitivity of rationals
   order. In the right to left, transivity alone completes the proof.

   \begin{code}

   _*_ : ℝ → ℝ → ℝ
   _*_ ((Lx , Rx) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x)
       ((Ly , Ry) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y)
     = (L , R) , inhabited-L , {!!} , rounded-left-L , {!!} , is-disjoint , {!!}
    where
     L : 𝓟 ℚ
     L p = (∃ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × p < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)) , ∃-is-prop
     R : 𝓟 ℚ
     R q = (∃ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × max₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d) < q) , ∃-is-prop

     x-values : ∥ (Σ a ꞉ ℚ , a ∈ Lx) × (Σ b ꞉ ℚ , b ∈ Rx) ∥
     x-values = binary-choice inhabited-left-x inhabited-right-x

     y-values : ∥ (Σ c ꞉ ℚ , c ∈ Ly) × (Σ d ꞉ ℚ , d ∈ Ry) ∥
     y-values = binary-choice inhabited-left-y inhabited-right-y

     xy-values : ∥ ((Σ a ꞉ ℚ , a ∈ Lx) × (Σ b ꞉ ℚ , b ∈ Rx)) × ((Σ c ꞉ ℚ , c ∈ Ly) × (Σ d ꞉ ℚ , d ∈ Ry)) ∥
     xy-values = binary-choice x-values y-values

     inhabited-L : inhabited-left L
     inhabited-L = ∥∥-rec ∃-is-prop I xy-values
      where
       I : ((Σ a ꞉ ℚ , a ∈ Lx) × (Σ b ꞉ ℚ , b ∈ Rx)) × ((Σ c ꞉ ℚ , c ∈ Ly) × (Σ d ꞉ ℚ , d ∈ Ry))
         → ∃ p ꞉ ℚ , ∃ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × p < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)
       I (((a , a<x) , (b , x<b)) , ((c , c<y) , (d , y<d))) = II (ℚ-no-least-element (min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)))
        where
         II : Σ p ꞉ ℚ , p < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)
            → _
         II (p , p<MIN) = ∣ p , ∣ (a , b , c , d) , a<x , x<b , c<y , y<d , p<MIN ∣ ∣

     rounded-left-L : rounded-left L
     rounded-left-L p = ltr , rtl
      where
       ltr : p ∈ L → ∃ p' ꞉ ℚ , (p < p') × p' ∈ L
       ltr p<xy = ∥∥-functor I p<xy
        where
         I : (Σ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × p < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d))
           → Σ p' ꞉ ℚ , p < p' × p' ∈ L
         I ((a , b , c , d) , a<x , x<b , c<y , y<d , p<MIN) = II (ℚ-dense fe p (min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)) p<MIN)
          where
           II : (Σ p' ꞉ ℚ , p < p' × p' < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d))
              → Σ p' ꞉ ℚ , p < p' × p' ∈ L
           II (p' , p<p' , p'<MIN) = p' , (p<p' , ∣ (a , b , c , d) , (a<x , x<b , c<y , y<d , p'<MIN) ∣)
       rtl : ∃ p' ꞉ ℚ , (p < p') × p' ∈ L → p ∈ L
       rtl p'-info = ∥∥-rec ∃-is-prop I p'-info
        where
         I : Σ p' ꞉ ℚ , (p < p') × p' ∈ L → p ∈ L
         I (p' , p<p' , p'<xy) = ∥∥-functor II p'<xy
          where
           II : Σ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × p' < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)
              → Σ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × p  < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)
           II ((a , b , c , d) , a<x , x<b , c<x , x<d , p'<MIN) = (a , b , c , d) , a<x , x<b , c<x , x<d , ℚ<-trans p p' (min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)) p<p' p'<MIN

     is-disjoint : disjoint L R
     is-disjoint p q (p<xy , xy<q) = {!!}

   \end{code}

   Here's the plan. We'll start by outlining the strategy in text, and
   later turn it into code.

   Given cuts $u$, $v$, define their product $uv$ as in the file. Our
   task is to show it satisfies the various properties.

   Given a rational $p$ and cut $u$, define $p\cdot u \in \mathbb R$ by:
   \begin{itemize}
   \item for $0$: $q < 0\cdot u$ iff $q < 0$ and $q > 0\cdot u$ iff $q > 0$.
   \item for $p > 0$: $q < p\cdot u$ iff $\tfrac qp < u$, define the
     upper pre-cut by applying the swapping symmetry (on pairs of
     $\mathbb Q$-propositions).
   \item for $q < 0$: define the pre-cut by swapping again. (Not sure
     symmetry is the right gadget to use here.)
   \end{itemize}

   \begin{lemma}
     The function $(\cdot) : \mathbb Q \times \mathrm{Precuts} \to
     \mathrm{Precuts}$ is a monoid actions, and it restricts to a group
     action on $\mathbb Q_{\neq 0}$.
   \end{lemma}

   \begin{lemma}
     $(\cdot)$ restrict to an action on dedkind cuts.
   \end{lemma}

   \begin{lemma}
     if $uv > 0$ then either:
     \begin{itemize}
     \item $u, v > 0$; or
     \item $u, v < 0$.
     \end{itemize}
   \end{lemma}
   \begin{proof}
     By definition, we have $p_1 < u < p_2$, $q_1 < u < q_2$ such that,
     for all $i,j \in \{1,2\}$: $0 < p_iq_j$.

     Assume one of the four rationals $r > 0$, wlog it is $p_1$. Since
     $p_1q_i > 0$, we have $q_i > 0$. By symmetry, $p_2 > 0$, so all four
     rationals are positive.

     Otherwise, all four rationals are negative.

     So all four rationals are either positive, or negative. wlog, assume
     they are all positive. In that case, $0 < p_1 < u$ and $0 < q_1 <
     v$, so $0 < u$ and $0 < v$.
   \end{proof}

   \begin{lemma}
     If let $u > 0$, $v > 0$ be cuts, $a \in \mathbb Q$. If $uv > a \geq
     0$ then we have some rationals $0 < s < u$ and $0 < t < v$ such that
     $a < st$.
   \end{lemma}
   \begin{proof}
     By assumption, we have some $p_1 < u < p_2$, $q_1 < u < q_2$
     rationals, such that $p_iq_j > a$.

     If $p_1, q_1 > 0$, we are done.  Otherwise, since $p_1q_1 > a \geq
     0$, we must have $p_1, q_1 < 0$, but $p_2 > u > 0$ so $p_2 > 0$, and
     symmetrically $q_2 > 0$. But then $0 > p_1q_2 > a \geq 0$,
     contradiction. Either way, we are done.
   \end{proof}

   \begin{lemma}
     Let $u, v > 0$ be cuts. If $uv < 1$ then we have some rationals $0 <
     s < u$ and $0 < t < v$ such that $st < 1$ and either $s < 1$ or $t <
     1$.
   \end{lemma}
   \begin{proof}
     Again, introduce $p_iq_j < 1$. Then $s := p_2$ and $t := q_2$
     completes the proof.
   \end{proof}

   \begin{lemma}
     Let $u,v > 0$ be cuts and $p$ rational. If $1 < uv < p$, then $1 < p$.
   \end{lemma}
   \begin{proof}
     By previous lemma, $1 < st$ with $0 < s < u$ and $0 < t < v$ rationals.

     By definition, there are some $a > u$, $b > v$ with $ab < p$.

     Since $u$ is a cut, $0 < s < a$, and symmetrically $0 < t < b$.
     Therefore $1 < st < ab < p$ and $1 < p$, as we wanted.
   \end{proof}

   \begin{lemma}
     Let $u$,$v$ be cuts. The precut $uv$ is disjoint.
   \end{lemma}

   \begin{proof}
     Assume $p < uv < q$.

     \begin{itemize}
     \item If $p = 0$, since $q > uv$, $q > 0 = p$ and we're done.
     \item If $p < 0$, $q > 0$, we are done.
     \item If $p > 0, q > 0$, divide by $p > 0$, use the previous lemma,
       and multiply by $p$ to get the result.
     \item If $p < 0, q < 0$, by symmetry we're in the previous case,
       done.
     \end{itemize}
   \end{proof}

   \begin{code}
     {-

     is-disjoint p q (p<xy , xy<q) = ∥∥-rec (ℚ<-is-prop p q) I (binary-choice p<xy xy<q)
      where
       I : (Σ (a₁ , b₁ , c₁ , d₁) ꞉ ℚ × ℚ × ℚ × ℚ , a₁ ∈ Lx × b₁ ∈ Rx × c₁ ∈ Ly × d₁ ∈ Ry × p < min₄ (a₁ ℚ* c₁) (a₁ ℚ* d₁) (b₁ ℚ* c₁) (b₁ ℚ* d₁))
         × (Σ (a₂ , b₂ , c₂ , d₂) ꞉ ℚ × ℚ × ℚ × ℚ , a₂ ∈ Lx × b₂ ∈ Rx × c₂ ∈ Ly × d₂ ∈ Ry × max₄ (a₂ ℚ* c₂) (a₂ ℚ* d₂) (b₂ ℚ* c₂) (b₂ ℚ* d₂) < q)
         → p < q
       I ( ((a₁ , b₁ , c₁ , d₁) , a₁<x , x<b₁ , c₁<x , x<d₁ , p<MIN₁) ,
           ((a₂ , b₂ , c₂ , d₂) , a₂<x , x<b₂ , c₂<x , x<d₂ , MAX₁<q) )
        = ℚ<-≤-trans fe p MIN₂ q p<MIN₂ (ℚ≤-trans fe MIN₂ MAX₂ q MIN₂≤MAX₂ MAX₂≤q)
        where
         a₃ b₃ c₃ d₃ : ℚ
         a₃ = max a₁ a₂
         b₃ = min b₁ b₂
         c₃ = max c₁ c₂
         d₃ = min d₁ d₂

         MIN₁ MAX₁ MIN₂ MAX₂ : ℚ
         MIN₁ = min₄ (a₁ ℚ* c₁) (a₁ ℚ* d₁) (b₁ ℚ* c₁) (b₁ ℚ* d₁)
         MAX₁ = max₄ (a₂ ℚ* c₂) (a₂ ℚ* d₂) (b₂ ℚ* c₂) (b₂ ℚ* d₂)
         MIN₂ = min₄ (a₃ ℚ* c₃) (a₃ ℚ* d₃) (b₃ ℚ* c₃) (b₃ ℚ* d₃)
         MAX₂ = max₄ (a₃ ℚ* c₃) (a₃ ℚ* d₃) (b₃ ℚ* c₃) (b₃ ℚ* d₃)

         MIN₁≤MIN₂ : MIN₁ ≤ MIN₂
         MIN₁≤MIN₂ = {!!}

         MAX₂≤MAX₁ : MAX₂ ≤ MAX₁
         MAX₂≤MAX₁ = {!!}

         p<MIN₂ : p < MIN₂
         p<MIN₂ = ℚ<-≤-trans fe p MIN₁ MIN₂ p<MIN₁ MIN₁≤MIN₂

         MIN₂≤MAX₂ : MIN₂ ≤ MAX₂
         MIN₂≤MAX₂ = min₄≤max₄ (a₃ ℚ* c₃) (a₃ ℚ* d₃) (b₃ ℚ* c₃) (b₃ ℚ* d₃)

         MAX₂<q : MAX₂ < q
         MAX₂<q = ℚ≤-<-trans fe MAX₂ MAX₁ q MAX₂≤MAX₁ MAX₁<q

         MAX₂≤q : MAX₂ ≤ q
         MAX₂≤q = ℚ<-coarser-than-≤ MAX₂ q MAX₂<q
   -}
   \end{code}
