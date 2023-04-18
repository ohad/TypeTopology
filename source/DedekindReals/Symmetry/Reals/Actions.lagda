Andrew Sneap and Ohad Kammar

Various actions on the reals

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
open import UF.Subsingletons-FunExt
open import UF.FunExt
open import UF.Equiv
open import UF.Powerset
open import UF.UniverseEmbedding

-- ought to not be needed eventually
open import UF.Univalence

open import Rationals.Type
open import Rationals.Order
open import Rationals.FractionsOrder

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
open import DedekindReals.Symmetry.GroupProperties

open import DedekindReals.Symmetry.Transitive

module DedekindReals.Symmetry.Reals.Actions
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
   open import DedekindReals.Symmetry.Reals.Type pe pt fe {𝓤}
   open import DedekindReals.Symmetry.Transport pe fe


   open import Rationals.Addition renaming (_+_ to _ℚ+_)
   open import Rationals.Negation
   open import Rationals.Multiplication renaming (_*_ to _ℚ*_)

   -- First, let's define some symmetries on the reals
   additive-ℚ : Group 𝓤₀
   additive-ℚ
     = ℚ
     , _ℚ+_
     , ℚ-is-set fe
     , ℚ+-assoc fe
     , 0ℚ
     , ℚ-zero-left-neutral fe
     , ℚ-zero-right-neutral fe
     , λ p → (- p)
           , (ℚ-inverse-sum-to-zero' fe p)
           , (ℚ-inverse-sum-to-zero  fe p)

   ℚ∘ : 𝓤₀ ̇
   ℚ∘ = Σ p ꞉ ℚ , p ≠ 0ℚ

   ℚ∘-is-set : is-set ℚ∘
   ℚ∘-is-set = sigma-is-set (ℚ-is-set fe)
     λ q → props-are-sets (negations-are-props fe)

   ≠0ℚ-is-prop : (p : ℚ) → is-prop (p ≠ 0ℚ)
   ≠0ℚ-is-prop p p≠₁0 p≠₂0 = nfe-by-fe fe (λ x → 𝟘-elim (p≠₁0 x))

   -- Must be somewhere!
   ℚ-dec-eq : (p q : ℚ) → (p ＝ q) ∔ (p ≠ q)
   ℚ-dec-eq p q with ℚ-trichotomous fe p q
   ... | inl p<q = inr (λ {refl → ℚ<-not-itself p p<q})
   ... | inr (inl p＝q) = inl p＝q
   ... | inr (inr p>q) = inr (λ {refl → ℚ<-not-itself p p>q})

   ℚ*-no-zero-divisors : (p q : ℚ) → (p ℚ* q ＝ 0ℚ) →
     (p ＝ 0ℚ) ∔ (q ＝ 0ℚ)
   ℚ*-no-zero-divisors p q p*q=0 with ℚ-dec-eq q 0ℚ
   ... | inl q=0 = inr q=0
   ... | inr q≠0 = inl
     (p
        ＝⟨ ℚ-mult-right-id fe p  ⁻¹  ⟩
      p ℚ* 1ℚ
        ＝⟨ ap (p ℚ*_) (qq'1 ⁻¹) ⟩
      p ℚ* (q ℚ* q')
        ＝⟨ ℚ*-assoc fe p q q' ⁻¹ ⟩
      (p ℚ* q ) ℚ* q'
        ＝⟨ ap (_ℚ* q') p*q=0 ⟩
      0ℚ ℚ* q'
        ＝⟨ ℚ-zero-left-is-zero fe q' ⟩
      0ℚ ∎)
     where
       q-inv : Σ q' ꞉ ℚ , q ℚ* q' ＝ 1ℚ
       q-inv = ℚ*-inverse fe q q≠0
       q' : ℚ
       q' = pr₁ q-inv
       qq'1 : q ℚ* q' ＝ 1ℚ
       qq'1 = pr₂ q-inv

   ℚ-one-not-zero : 1ℚ ≠ 0ℚ
   ℚ-one-not-zero 1=0 = ℚ-zero-not-one fe (1=0 ⁻¹)

   multiplicative-ℚ : Group 𝓤₀
   multiplicative-ℚ
     = ℚ∘
     , (λ (p , p≠0) (q , q≠0) → (p ℚ* q)
       , cases
           p≠0
           q≠0
           ∘ (ℚ*-no-zero-divisors p q) )
     , ℚ∘-is-set
     , (λ (x , _) (y , _) (z , _) →
          to-subtype-＝
            ≠0ℚ-is-prop
            (ℚ*-assoc fe x y z))
     , (1ℚ , ℚ-one-not-zero)
     , (λ (x , _) → to-subtype-＝
         ≠0ℚ-is-prop
         (ℚ-mult-left-id fe x))
     , (λ (x , _) → to-subtype-＝
         ≠0ℚ-is-prop
         (ℚ-mult-right-id fe x))
     , λ (x , x≠0) →
         let x' = multiplicative-inverse fe x x≠0
         in (x'
         , λ x'=0 → ℚ-one-not-zero
           (1ℚ
              ＝⟨ ℚ*-inverse-product-is-one fe x x≠0 ⁻¹ ⟩
            x ℚ* x'
              ＝⟨ ap (x ℚ*_) x'=0 ⟩
            (x ℚ* 0ℚ)
              ＝⟨ ℚ-zero-right-is-zero fe x ⟩
            0ℚ ∎))
       , to-subtype-＝
           ≠0ℚ-is-prop
           (x' ℚ* x
             ＝⟨ ℚ*-comm x' x ⟩
           x ℚ* x'
             ＝⟨ ℚ*-inverse-product-is-one fe x x≠0 ⟩
            1ℚ ∎)
       , to-subtype-＝
           ≠0ℚ-is-prop
           (ℚ*-inverse-product-is-one fe x x≠0)

   ℚ∘-pos : 𝓟 ℚ∘
   ℚ∘-pos (p , _) = 0ℚ < p , ℚ<-is-prop 0ℚ p

   instance
     canonical-map-ℚ∘-to-ℚ : Canonical-Map ℚ∘ ℚ
     ι {{canonical-map-ℚ∘-to-ℚ}} = pr₁


   open import DedekindReals.Symmetry.Subgroups pe pt fe
   open import DedekindReals.Symmetry.Subactions pe fe

   -- This ought to be in Rationals.Order
   ℚ-pos-non-zero : (p : ℚ) → (p>0 : 0ℚ < p) → ¬ (p ＝ 0ℚ)
   ℚ-pos-non-zero p p>0 p=0 = ℚ<-not-itself 0ℚ (transport (0ℚ <_) p=0 p>0)

   multiplicative-ℚ+-subgroup
     : Subgroups' multiplicative-ℚ
   multiplicative-ℚ+-subgroup = ℚ∘-pos ,
     ( lift _ (0 , refl)
     , (λ p q p>0 q>0 →
         (ℚ<-pos-multiplication-preserves-order
           (ι p) (ι q) p>0 q>0))
     , (λ { (p , p≠0) p>0 →
            (multiplicative-inverse-preserves-pos fe
              p (p>0) p≠0)
          }))

   multiplicative-ℚ+ : Group 𝓤₀
   multiplicative-ℚ+ = induced-group' multiplicative-ℚ multiplicative-ℚ+-subgroup

   open import DedekindReals.Addition pe pt fe
     renaming (_+_ to _ℝ+_; -_ to ℝ-_)
   additive-ℝ' : Group 𝓤₁
   -- TODO: transport structure
   additive-ℝ'
     = ℝ'
     , (λ r s → ⌜ ℝ≃ℝ' ⌝ (⌜ ℝ≃ℝ' ⌝⁻¹ r ℝ+ ⌜ ℝ≃ℝ' ⌝⁻¹ s))
     , ℝ'-is-set
     , {!
     !}
     , ι 0ℝ
     , {!!}
     , {!!}
     , λ x →
       (ι (ℝ- ι x))
     , {!!}
     , {!!}

   ℚ+'∣ℝ' : Action' additive-ℚ
   ℚ+'∣ℝ'
     = ℝ'
     , (λ lp r → ι lp ·⟨ additive-ℝ' ⟩ r)
     , ℝ'-is-set
     , {!!}
     , {!!}

   ℚ₊ : 𝓤₀ ̇
   ℚ₊ = ⟨ multiplicative-ℚ+ ⟩

   instance
     canonical-map-ℚ₊-to-ℚ : Canonical-Map ℚ₊ ℚ
     ι {{canonical-map-ℚ₊-to-ℚ}} = pr₁ ∘ pr₁

   -- can do away with some of the projection reshuffling if
   -- we define the monoid action instead

   -- It's easier to go this way :(
   ℚ∘* : Group 𝓤₀
   ℚ∘* = multiplicative-ℚ

   ℚ₊*◃ℚ*' : Subgroups' multiplicative-ℚ
   ℚ₊*◃ℚ*' = ℚ∘-pos
     , (unit-closed' multiplicative-ℚ multiplicative-ℚ+-subgroup)
     , (mult-closed' multiplicative-ℚ multiplicative-ℚ+-subgroup)
     , (inv-closed' multiplicative-ℚ multiplicative-ℚ+-subgroup)


   ℚ₊* : Group 𝓤₀
   ℚ₊* = induced-group' multiplicative-ℚ ℚ₊*◃ℚ*'

   scale-pred : ⟨ multiplicative-ℚ ⟩ → 𝓟 ℚ → 𝓟 ℚ
   scale-pred p P q
       -- This way around works better with left actions
     = P (pr₁ (inv multiplicative-ℚ p) ℚ* q)

   ℚ∘*∣ℚ : Action (ℚ∘* ᵒᵖ)
   ℚ∘*∣ℚ
     = ℚ
     , (λ pnz x → pr₁ (inv ℚ∘* pnz) ℚ* x)
     , ℚ-is-set fe
     , (λ pnz@(p , p≠0) qnz@(q , q≠0) x →
       let (p' , _) = inv ℚ∘* pnz
           (q' , _) = inv ℚ∘* qnz
       in pr₁ (inv ℚ∘* (qnz ·⟨ ℚ∘* ⟩ pnz)) ℚ* x
                ＝⟨ ap (λ r → (pr₁ r) ℚ* x)
                    (inv-reverses-multiplication
                    ℚ∘* qnz pnz) ⟩
              (p' ℚ* q') ℚ* x
                ＝⟨ ℚ*-assoc fe p' q' x ⟩
              p' ℚ* (q' ℚ* x)  ∎)
     , λ x → pr₁ (inv ℚ∘* (unit ℚ∘*)) ℚ* x
         ＝⟨ ap (λ r → pr₁ r ℚ* x)
                (inv-unit-unit ℚ∘*)  ⟩
         1ℚ ℚ* x
         ＝⟨ ℚ-mult-left-id fe x  ⟩
         x ∎

   open GroupConstructions

   -- Now starts the real work, hopefully
   ℚ*'∣𝓟ℚ : Action' ℚ∘*
   ℚ*'∣𝓟ℚ = RelLiftActionᵒᵖ ℚ∘* ℚ∘*∣ℚ

   ℚ₊*∣𝓟ℚ : Action' ℚ₊*
   ℚ₊*∣𝓟ℚ = induced-action ℚ∘* ℚ₊*◃ℚ*' ℚ*'∣𝓟ℚ

   ℚ₊*∣𝓟ℚ-inhabited-invariant :
     prop-is-invariant ℚ₊*
                       ℚ₊*∣𝓟ℚ
                       inhabited-pred
   ℚ₊*∣𝓟ℚ-inhabited-invariant ((g , g≠0) , g>0) L
     = let (g'' , g''≠0) = inv multiplicative-ℚ (g , g≠0)
       in (∥∥-induction
       (λ _ → ∃-is-prop)
       λ (p , Lp) →
       let u : ⟨ L (g'' ℚ* (g ℚ* p)) ⟩
           u = transport (λ ℓ → ⟨ L ℓ ⟩)
               (p
                  ＝⟨ ℚ-mult-left-id fe p ⁻¹ ⟩
                1ℚ ℚ* p
                  ＝⟨ ap (_ℚ* p)
                      (ap pr₁
                      (inv-left multiplicative-ℚ
                        (g , g≠0))
                      ⁻¹) ⟩
                (g'' ℚ* g) ℚ* p
                  ＝⟨ ℚ*-assoc fe g'' g p ⟩
                g'' ℚ* (g ℚ* p) ∎
               )
               Lp
       in ∣ g ℚ* p  , u ∣)

   pr-⇒ : {𝓤 𝓥 : Universe} {p : Ω 𝓤} → {q : Ω 𝓥}  →
     ⟨ p ⇔Ω q ⟩ → ⟨ p ⇒Ω q ⟩
   pr-⇒ = pr₁

   pr-⇐ : {𝓤 𝓥 : Universe} {p : Ω 𝓤}  → {q : Ω 𝓥}  →
     ⟨ p ⇔Ω q ⟩ → ⟨ q ⇒Ω p ⟩
   pr-⇐ = pr₂

   -1ℚ<0 : - 1ℚ < 0ℚ
   -1ℚ<0 = ℚ<-negative-is-negative 0 1

   -1ℚ≠0 : ¬ (- 1ℚ ＝ 0ℚ)
   -1ℚ≠0 -1ℚ=0ℚ = ℚ<-not-itself (- 1ℚ)
     (transport ((- 1ℚ) <ℚ_) (-1ℚ=0ℚ ⁻¹) -1ℚ<0)

   ℚ<-pos-multiplication-monotone : (p q q' : ℚ) → p > 0ℚ →
     q < q' → p ℚ* q < p ℚ* q'
   ℚ<-pos-multiplication-monotone p q q' p>0 q<q'
     = p ℚ* q
       ＝⟨ unit-right additive-ℚ (p ℚ* q) ⁻¹ ⟩
       (p ℚ* q ℚ+ 0ℚ)
       ≺⟨ _<_ ∣
         ℚ<-addition-preserves-order-left
         (p ℚ* q) 0ℚ (p ℚ* ((- q) ℚ+ q')) 0<p[-q+q'] ⟩
       (p ℚ* q ℚ+ (p ℚ* ((- q) ℚ+ q')))
         ＝⟨ pq+p[-q+q']=pq' ⟩
       p ℚ* q'  ∎

     where
       0<-q+q' : 0ℚ < (- q) ℚ+ q'
       0<-q+q' =
         0ℚ
           ＝⟨ inv-left additive-ℚ q ⁻¹ ⟩
         (- q) ℚ+ q
           ≺⟨ _<_ ∣ ℚ<-addition-preserves-order-left
             (- q) q q' q<q' ⟩
         (- q) ℚ+ q'
           ＝⟨ refl ⟩
         (- q) ℚ+ q' ∎
       0<p[-q+q'] : 0ℚ < p ℚ* ((- q) ℚ+ q')
       0<p[-q+q'] = ℚ<-pos-multiplication-preserves-order
                  p ((- q) ℚ+ q') p>0 0<-q+q'
       pq+p[-q+q']=pq' :
         p ℚ* q ℚ+ (p ℚ* ((- q) ℚ+ q')) ＝ p ℚ* q'
       pq+p[-q+q']=pq' =
         p ℚ* q ℚ+ (p ℚ* ((- q) ℚ+ q'))
            ＝⟨ ℚ-distributivity fe
                 p q ((- q) ℚ+ q') ⁻¹ ⟩
          p ℚ* (q ℚ+ ((- q) ℚ+ q'))
            ＝⟨ ap (p ℚ*_) (assoc additive-ℚ q (- q) q' ⁻¹) ⟩
          p ℚ* ((q ℚ+ (- q)) ℚ+ q')
            ＝⟨ ap (λ u → p ℚ*(u ℚ+ q'))
                (inv-right additive-ℚ q) ⟩
          p ℚ* (0ℚ ℚ+ q')
            ＝⟨ ap (p ℚ*_) (unit-left additive-ℚ q') ⟩
          p ℚ* q' ∎

   ℚ-negate-equation : (a b : ℚ) → a < b → - b < - a
   ℚ-negate-equation a b a<b =
     - b
       ＝⟨ -- calculate as follows:
           - b
             ＝⟨ unit-right additive-ℚ (- b) ⁻¹ ⟩
           (- b) ℚ+ 0ℚ
             ＝⟨ ap ((- b) ℚ+_)
                 (inv-right additive-ℚ a ⁻¹) ⟩
           (- b) ℚ+ (a ℚ+ (- a))
             ＝⟨ assoc additive-ℚ (- b) a (- a) ⁻¹ ⟩
           ((- b) ℚ+ a) ℚ+ (- a) ∎
         ⟩
     ((- b) ℚ+ a) ℚ+ (- a)
       ≺⟨ _<_ ∣ ℚ<-addition-preserves-order-right
                 (( - b) ℚ+ a) ((- b) ℚ+ b) (- a)
                 (ℚ<-addition-preserves-order-left
                 (- b) a b a<b) ⟩
     ((- b) ℚ+ b) ℚ+ (- a)
       ＝⟨ -- calculate as follows:
           ((- b) ℚ+ b) ℚ+ (- a)
             ＝⟨ ap (_ℚ+ (- a))
                (inv-left additive-ℚ b) ⟩
           0ℚ ℚ+ (- a)
             ＝⟨ unit-left additive-ℚ (- a) ⟩
           - a ∎
         ⟩
     - a ∎


   ℚ<-neg-multiplication-antitone : (p q q' : ℚ) → p < 0ℚ →
     q < q' → p ℚ* q > p ℚ* q'
   ℚ<-neg-multiplication-antitone p q q' p<0 q<q' =
     (p ℚ* q')
       ＝⟨ ℚ*-minus-minus fe p q' ⁻¹ ⟩
     (- p) ℚ* (- q')
       ≺⟨ _<_ ∣ -p*-q'<-p*-q ⟩
     (- p) ℚ* (- q)
       ＝⟨ ℚ*-minus-minus fe p q ⟩
     p ℚ* q ∎
     where
       -q'<-q : - q' < - q
       -q'<-q = ℚ-negate-equation q q' q<q'
       -p>0 : - p > 0ℚ
       -p>0 = ℚ-negate-equation p 0ℚ p<0
       -p*-q'<-p*-q : (- p) ℚ* (- q') < (- p) ℚ* (- q)
       -p*-q'<-p*-q = ℚ<-pos-multiplication-monotone
          (- p) (- q') (- q) -p>0 -q'<-q

   ℚ-mult-minus-one-negates : (p : ℚ) →
     (- 1ℚ) ℚ* p ＝ - p
   ℚ-mult-minus-one-negates p =
     (- 1ℚ) ℚ* p
        ＝⟨ ℚ-negation-dist-over-mult-left fe 1ℚ p ⟩
     - (1ℚ ℚ* p)
                -- need to use multiplicative monoid
                -- structure we haven't defined
        ＝⟨ ap -_ (ℚ-mult-left-id fe p) ⟩
     - p ∎


   ℚ<-neg-antitone : (p q : ℚ) →
     p < q → (- q) < (- p)
   ℚ<-neg-antitone p q p<q =
     - q
       ＝⟨ ℚ-mult-minus-one-negates q ⁻¹ ⟩
     (- 1ℚ) ℚ* q
       ≺⟨ _<_ ∣ ℚ<-neg-multiplication-antitone
                (- 1ℚ) p q -1ℚ<0 p<q ⟩
     (- 1ℚ) ℚ* p
       ＝⟨ ℚ-mult-minus-one-negates p ⟩
     - p ∎



   -- TODO: maybe we can use symmetric programming to
   -- discharge these?

   p/q<l⇔p<ql : (((q , q≠0) , q>0) : ⟨ ℚ₊* ⟩) → (p r : ℚ) →
         ⟨ ℚ< (ι (inv multiplicative-ℚ (q , q≠0)) ℚ* p , r) ⇔Ω
          (ℚ< (p , q ℚ* r)) ⟩
   p/q<l⇔p<ql ((q , q≠0) , q>0) p r
     = let ((q' , q'≠0) , q'>0)  = inv ℚ₊* ((q , q≠0) , q>0) in
       (λ p/q<r →
         p
         ＝[ --calculate:
             p
               ＝⟨ ℚ-mult-left-id fe p ⁻¹ ⟩
             1ℚ ℚ* p
               ＝⟨ ap (λ x → ι x ℚ* p)
                    (inv-right ℚ∘* (q , q≠0)) ⁻¹ ⟩
             (q ℚ* q') ℚ* p
               ＝⟨ ℚ*-assoc fe q q' p ⟩
             q ℚ* (q' ℚ* p) ∎
           ]
         q ℚ* (q' ℚ* p)
           ≺⟨ _<_ ∣ ℚ<-pos-multiplication-monotone
                    q (q' ℚ* p) r q>0 p/q<r ⟩
         q ℚ* r ∎)
     , λ p<qr →
         q' ℚ* p
           ≺⟨ _<_ ∣ ℚ<-pos-multiplication-monotone
                    q' p (q ℚ* r) q'>0 p<qr ⟩
         q' ℚ* (q ℚ* r)
           ＝[ -- calculate
               q' ℚ* (q ℚ* r)
                 ＝⟨ ℚ*-assoc fe q' q r ⁻¹ ⟩
               (q' ℚ* q) ℚ* r
                 ＝⟨ ap (λ x → ι x ℚ* r)
                     (inv-left ℚ∘* (q , q≠0)) ⟩
               1ℚ ℚ* r
                 ＝⟨ ℚ-mult-left-id fe r ⟩
               r ∎ ]
         r ∎

   x∈pL⇔x/p∈L : (x p : ℚ) → (L : 𝓟 ℚ) →
     (p≠0 : ¬ (p ＝ 0ℚ)) →
     ⟨ ((p , p≠0) ◂⟨ multiplicative-ℚ ∣ ℚ*'∣𝓟ℚ ⟩ L) x ⇔Ω
       L ( ι (inv multiplicative-ℚ (p , p≠0)) ℚ* x) ⟩
   x∈pL⇔x/p∈L x p L p≠0
     = id
     , id


   ℚ₊*∣𝓟ℚ-rounded-invariant :
     prop-is-invariant ℚ₊*
                       ℚ₊*∣𝓟ℚ
                       (rounded-wrt ℚ<)
   ℚ₊*∣𝓟ℚ-rounded-invariant gp@((g , g≠0) , g>0) L L-rounded p
     = let ((g' , g'≠0), g'>0) = inv ℚ₊* gp
           (Lg'p⇒∃ , Lg'p⇐∃) = L-rounded (g' ℚ* p)
       in
       (λ Lg'p → ∥∥-induction
                  (λ _ → ∃-is-prop)
                  (λ (q , g'p<q , Lq) →
                    ∣ g ℚ* q
                      , pr-⇒ (p/q<l⇔p<ql gp p q) g'p<q
                        -- we have Lq
                        -- we need L(g' * (g * q))
                      , transport (λ x → ⟨ L x ⟩)
                          (q
                            ＝⟨ ℚ-mult-left-id fe q ⁻¹ ⟩
                          1ℚ ℚ* q
                            ＝⟨ ap (λ x → ι x ℚ* q)
                            (inv-left multiplicative-ℚ
                              (g , g≠0)) ⁻¹ ⟩
                          (g' ℚ* g) ℚ* q
                          ＝⟨ ℚ*-assoc fe g' g q ⟩
                           g' ℚ* (g ℚ* q) ∎)
                          Lq ∣)
                  (Lg'p⇒∃ Lg'p))
       , ∥∥-induction
           (λ _ → holds-is-prop (L (pr₁ (inv ℚ∘* (g , g≠0)) ℚ* p)))
           (λ (q , p<q , Lg'q) →
                 (Lg'p⇐∃ ∣ g' ℚ* q
                 , ℚ<-pos-multiplication-monotone
                     g' p q g'>0 p<q
                 , Lg'q ∣ ))

   S₂ᵒᵖ∣ℚ : Action (S₂ ᵒᵖ)
   S₂ᵒᵖ∣ℚ
     = ℚ
     , (λ { id∈S₂ x → x
          ; flip  x → - x
          })
     , ℚ-is-set fe
     , (λ { g id∈S₂ x → refl
          ; id∈S₂ flip x → refl
          ; flip flip x → ℚ-minus-minus fe x
          })
     , λ x → refl

   S₂∣𝓟ℚ : Action' S₂
   S₂∣𝓟ℚ = RelLiftActionᵒᵖ S₂ S₂ᵒᵖ∣ℚ

   -- The point: rounded-right is not invariant, but rounded-wrt it

   ℚ□ : 𝓟 (Rel)
   ℚ□ = ((only (𝓟-is-set' fe pe) ℚ<) ⊕
          (only (𝓟-is-set' fe pe) ℚ>))
          -- Show that ℚ< ≠ ℚ>
          λ { .ℚ< (refl , ℚ>=ℚ<) → ℚ<-not-itself 0ℚ
            (ℚ<-trans 0ℚ 1ℚ 0ℚ
              (ℚ-zero-less-than-positive 0 1)
              (transport (λ P → ⟨ P (1ℚ , 0ℚ) ⟩)
                ℚ>=ℚ<
                (ℚ-zero-less-than-positive 0 1)))}


   S₂∣ℚ□◃Rel : prop-is-invariant S₂ S₂∣Rel ℚ□
   S₂∣ℚ□◃Rel id∈S₂ P prf = prf
   S₂∣ℚ□◃Rel flip .ℚ< (inl refl) = inr refl
   S₂∣ℚ□◃Rel flip .(opposite ℚ<) (inr refl)
     = inl refl

   S₂∣ℚ□ : Action' S₂
   S₂∣ℚ□ = subaction S₂ S₂∣Rel ℚ□ S₂∣ℚ□◃Rel

   -- Plan:

   S₂'∣ℚ□×𝓟ℚ : Action' S₂
   S₂'∣ℚ□×𝓟ℚ = S₂∣ℚ□ ⊙ S₂∣𝓟ℚ

   -- There ought to be a proof using the fact that
   -- the logical connectives are equivariant in some sense
   rounded-wrt-invariant-wrt-flip-ℚ< :
     (L : 𝓟 ℚ) →
     prop-is-invariant-wrt-at
       S₂ S₂'∣ℚ□×𝓟ℚ
       (λ {((R , ℚ<∨ℚ>) , L) → rounded-wrt R  L })
       flip
       ((ℚ< , inl refl) , L)
   rounded-wrt-invariant-wrt-flip-ℚ< L L-rounded p
     = (λ L-p → ∥∥-induction
         (λ _ → ∃-is-prop)
         (λ (q , -p<q , Lq) →
           ∣ - q
           , - q
                 ≺⟨ _<_ ∣ ℚ<-neg-antitone (- p) q -p<q ⟩
               - (- p)
                 ＝[ ℚ-minus-minus fe p ⁻¹ ]
               p ∎
           , transport (λ r → ⟨ L r ⟩)
               (ℚ-minus-minus fe q)
               Lq  ∣)
         (pr-⇒ (L-rounded (- p)) L-p))
     , ∥∥-induction
          (λ _ → holds-is-prop
            ((flip ◂⟨ S₂ ∣ S₂∣𝓟ℚ ⟩ L)  p))
          λ (q , q<p , L-q) →
            pr-⇐ (L-rounded (- p))
                 ∣ - q , ℚ<-neg-antitone q p q<p , L-q ∣
   -- blech, we ought to use symmetry
   rounded-wrt-invariant-wrt-flip-ℚ> :
     (L : 𝓟 ℚ) →
     prop-is-invariant-wrt-at
       S₂ S₂'∣ℚ□×𝓟ℚ
       (λ {((R , ℚ<∨ℚ>) , L) → rounded-wrt R  L })
       flip
       ((ℚ> , inr refl) , L)
   rounded-wrt-invariant-wrt-flip-ℚ> L L-rounded p
     = (λ L-p → ∥∥-induction
         (λ _ → ∃-is-prop)
         (λ (q , -p>q , Lq) →
           ∣ - q
           ,  - q
                 ≺⟨ _>_ ∣ ℚ<-neg-antitone q (- p) -p>q ⟩
               - (- p)
                 ＝[ ℚ-minus-minus fe p ⁻¹ ]
               p ∎
           ,  transport (λ r → ⟨ L r ⟩)
               (ℚ-minus-minus fe q)
               Lq  ∣)
         (pr-⇒ (L-rounded (- p)) L-p))
     , ∥∥-induction
          (λ _ → holds-is-prop
            ((flip ◂⟨ S₂ ∣ S₂∣𝓟ℚ ⟩ L)  p))
          λ (q , q<p , L-q) →
            pr-⇐ (L-rounded (- p))
                 ∣ - q ,  ℚ<-neg-antitone p q q<p  , L-q ∣

   rounded-wrt-invariant :
     prop-is-invariant S₂
                       S₂'∣ℚ□×𝓟ℚ
                       λ {((R , ℚ<∨ℚ>) , L) →
                         rounded-wrt R  L }
   rounded-wrt-invariant id∈S₂ ((R , ℚ<∨ℚ>) , L) L-rounded
     = L-rounded
   rounded-wrt-invariant flip ((.ℚ< , inl refl) , L) L-ℚ<-rounded
     = rounded-wrt-invariant-wrt-flip-ℚ< L L-ℚ<-rounded
   rounded-wrt-invariant flip ((.ℚ> , inr refl) , L) L-ℚ>-rounded
     = rounded-wrt-invariant-wrt-flip-ℚ> L L-ℚ>-rounded



   -- The reason this argument works:
   S₂-ℚ₊*-commute :
     actions-commute S₂ ℚ₊* S₂∣𝓟ℚ ℚ₊*∣𝓟ℚ
   S₂-ℚ₊*-commute id∈S₂ ((h , h≠0) , h>0) L = refl
   S₂-ℚ₊*-commute flip hp@((h , h≠0) , h>0) L = nfe-by-fe fe λ p →
     let ((h' , h'≠0) , h'>0) = inv ℚ₊* hp in
     ap  L (
        h' ℚ* (- p)
       ＝⟨ ℚ-negation-dist-over-mult-right fe h' p ⟩
       - (h' ℚ* p) ∎
        )

   S₂⊗ℚ₊*∣𝓟ℚ : Action' (S₂ ⊗ ℚ₊*)
   S₂⊗ℚ₊*∣𝓟ℚ = merge S₂       S₂∣𝓟ℚ
                         ℚ₊* ℚ₊*∣𝓟ℚ
                         S₂-ℚ₊*-commute

   ℚ₊*∣𝓟ℚ-rounded-right-invariant :
     prop-is-invariant ℚ₊* ℚ₊*∣𝓟ℚ
                       (rounded-wrt ℚ>)

   ℚ₊*∣𝓟ℚ-rounded-right-invariant
     g@((g₀ , g≠0) , g>0) L L-rounded-right p
     = transport rounded-right [g◂Lᵒᵖ]ᵒᵖ=g◂L
       [g◂Lᵒᵖ]ᵒᵖ-rounded-right p
     where
       Lᵒᵖ : 𝓟 ℚ
       Lᵒᵖ = flip ◂⟨ S₂ ∣ S₂∣𝓟ℚ ⟩ L

       Lᵒᵖ-rounded-left : rounded-left Lᵒᵖ
       Lᵒᵖ-rounded-left = rounded-wrt-invariant
                          flip ((ℚ> , inr refl) , L)
                          L-rounded-right
       g◂Lᵒᵖ : 𝓟 ℚ
       g◂Lᵒᵖ = g ◂⟨ ℚ₊* ∣ ℚ₊*∣𝓟ℚ ⟩ Lᵒᵖ
       g◂Lᵒᵖ-rounded-left : rounded-left g◂Lᵒᵖ
       g◂Lᵒᵖ-rounded-left
         = ℚ₊*∣𝓟ℚ-rounded-invariant g Lᵒᵖ Lᵒᵖ-rounded-left
       [g◂Lᵒᵖ]ᵒᵖ : 𝓟 ℚ
       [g◂Lᵒᵖ]ᵒᵖ = flip ◂⟨ S₂ ∣ S₂∣𝓟ℚ ⟩ g◂Lᵒᵖ
       [g◂Lᵒᵖ]ᵒᵖ-rounded-right : rounded-right [g◂Lᵒᵖ]ᵒᵖ
       [g◂Lᵒᵖ]ᵒᵖ-rounded-right
         = rounded-wrt-invariant
                          flip ((ℚ< , inl refl) , g◂Lᵒᵖ)
                          g◂Lᵒᵖ-rounded-left
       g◂L : 𝓟 ℚ
       g◂L = g ◂⟨ ℚ₊* ∣  ℚ₊*∣𝓟ℚ ⟩ L
       [g◂Lᵒᵖ]ᵒᵖ=g◂L : [g◂Lᵒᵖ]ᵒᵖ ＝ g◂L
       [g◂Lᵒᵖ]ᵒᵖ=g◂L = nfe-by-fe fe (λ p →
         let ((g' , g'≠0) , g'>0) = inv ℚ₊* g
         in ap L
         (- (g' ℚ* (- p))
           ＝⟨ ap -_ (ℚ-negation-dist-over-mult-right fe g' p) ⟩
           - (- (g' ℚ* p))
           ＝⟨ ℚ-minus-minus fe (g' ℚ* p) ⁻¹ ⟩
           g' ℚ* p ∎
         ))

   -- Should be done more generally

   ℚ*'∣pre-cut-action : action-structure multiplicative-ℚ pre-cut
   ℚ*'∣pre-cut-action lpnz r
     with (p , p≠0) ← lpnz | ℚ-trichotomous fe p 0ℚ
   ... | inl p>0 = {!!}
   ... | inr p<0 = {!!}

   ℚ*'∣pre-cut : Action' multiplicative-ℚ
   ℚ*'∣pre-cut
     = pre-cut
     , (λ lq x → {!!})
     , {!!}
     , {!!}
     , {!!}
