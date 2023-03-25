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



module SymmetricProgramming (G : Group 𝓤) (A : Action G) where
  -- heterogeneous equality
  data _≈_ {X : 𝓤 ̇} (x : X) : {Y : 𝓤 ̇} → (y : Y) → 𝓤 ⁺ ̇
    where
    NB:_since_ : forall {Y} (y : Y) →
      (prf : X ＝ Y) → transport id prf x ＝ y → x ≈ y

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

  inv-involutive : (g : ⟨ G ⟩) → inv G (inv G g) ＝ g
  inv-involutive g = {!!} -- fun to be had here

  as-action : {⟨B⟩ : ⟨ A ⟩ → 𝓤 ̇ } →
    indexed-action-over ⟨B⟩ → Action-structure G (Σ ⟨B⟩)
  as-action (_·_ , axioms)
    = (λ g → λ { (a , b) → (g ◂⟨ G ∣ A ⟩ a)  , (g · b)})
    , {!!} -- lots of HoTT fun to be had here

  ⟨_∣_⟩-indexed-action : 𝓤 ⁺ ̇
  ⟨_∣_⟩-indexed-action = Σ indexed-action-over

  indexed-action-op-syntax : ((⟨B⟩ , rest) : ⟨_∣_⟩-indexed-action) →
    indexed-action-structure-over  ⟨B⟩
  indexed-action-op-syntax B = indexed-action-op B
  syntax indexed-action-op-syntax B g y = g ◃⟨ B ⟩ y

  -- The workhorse: two views

  data _~[_]~* : ⟨ A ⟩ → ⟨ G ⟩ → 𝓤 ̇ where
    take : (g : ⟨ G ⟩ ) → (x : ⟨ A ⟩) →
      (g ◂⟨ G ∣ A ⟩ x) ~[ inv G g ]~*

  data _~[[_]]~_ : ⟨ A ⟩ → ⟨ G ⟩ → ⟨ A ⟩ → 𝓤 ̇ where
    act : (g : ⟨ G ⟩) → (a : ⟨ A ⟩) → a ~[[ g ]]~ (g ◂⟨ G ∣ A ⟩ a)

  invert-action : {g : _} {x y : _} → x ~[[ g ]]~ y → y ~[[ inv G g ]]~ x
  invert-action (act g a) = {!!} -- fun to be had here

  invert-inv-action : {g : _} {x y : _} → y ~[[ inv G g ]]~ x → x ~[[ g ]]~ y
  invert-inv-action {g} {x} {y} view =
    transport (λ h → x ~[[ h ]]~ y)
    (inv-involutive g)
    (invert-action view)


  transport2 : {X Y : 𝓤 ̇ } (A : X → Y → 𝓥 ̇ ) {x1 x2 : X} {y1 y2 : Y}
          → x1 ＝ x2 → y1 ＝ y2 → A x1 y1 → A x2 y2
  transport2 A refl refl x = x

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
  inv-act-inverse-right g a = {!!}

  ekat : (g : ⟨ G ⟩) → (a : ⟨ A ⟩) → a ~[ g ]~*
  ekat g a = transport2 (λ x h → x ~[ h ]~*)
    (inv-act-inverse-left g a)
    (inv-involutive g)
    (take (inv G g) (g ◂⟨ G ∣ A ⟩ a))

  return-fun : ((⟨B⟩ , foo) : ⟨_∣_⟩-indexed-action) → (a : ⟨ A ⟩ ) →
           (g : ⟨ G ⟩) →
           (⟨B⟩ (g ◂⟨ G ∣ A ⟩ a) → ⟨B⟩ a)
  return-fun B a g result with (ekat g a)
  return-fun B@(⟨B⟩ , _) .(h ◂⟨ G ∣ A ⟩ x) .(inv G h) result | take h x
    = transport ⟨B⟩ (inv-act-inverse-right h _) (h ◃⟨ B ⟩ result)

  out-log : ((⟨B⟩ , foo) : ⟨_∣_⟩-indexed-action) → (a : ⟨ A ⟩ ) →
           (g : ⟨ G ⟩) →
           (a ~[ g ]~*)
           × (⟨B⟩ (g ◂⟨ G ∣ A ⟩ a) → ⟨B⟩ a)
  out-log B a g = ekat g a , return-fun B a g


{-with (ekat g a)
         ... | foo = ?-}

module Multiplication
         (pe : Prop-Ext)
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where

   open import Rationals.Multiplication renaming (_*_ to _ℚ*_)
   open import Rationals.MinMax fe
   open import DedekindReals.Type pe pt fe
   open PropositionalTruncation pt

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
