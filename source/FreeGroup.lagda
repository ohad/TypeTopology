Martin Escardo, 04 January 2021.

Ongoing joint work with Marc Bezem, Thierry Coquand, and Peter Dybjer.

We construct free groups in HoTT/UF in Agda without HIT's other than
propositional truncation.

Based on Richman's book on constructive algebra.

For the moment this file is not for public consumption, but it is
publicly visible.

This is part of the Martin Escardo's Agda development TypeTopology,
whose philosophy is to be Spartan. At the moment we are a bit
Athenian, though, although we intend to fix this in the
future.

\begin{code}

{-# OPTIONS --without-K --safe #-} -- --exact-split

\end{code}

NB. This repository is supposed to use exact-split, but even though
everything has been developed using case-split, the exact-split check
fails (in Agda 2.6.1) in the helper function f of the function
churros. This seems to be a bug.

\begin{code}

module FreeGroup where

open import SpartanMLTT
open import Two
open import Two-Properties

open import UF-PropTrunc
open import UF-Univalence
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-UA-FunExt
open import UF-FunExt

\end{code}

It is possible to work with lists *defined* from the ingredients of
our Spartan MLTT (see the module Fin.lagda). For the moment we are
Athenian in this respect:

\begin{code}

data List {𝓤} (X : 𝓤 ̇ ) : 𝓤 ̇  where
 [] : List X
 _∷_ : X → List X → List X

infixr 3 _∷_

equal-heads : {X : 𝓤 ̇ } {x y : X} {s t : List X}
            → x ∷ s ≡ y ∷ t
            → x ≡ y
equal-heads refl = refl

equal-tails : {X : 𝓤 ̇ } {x y : X} {s t : List X}
            → x ∷ s ≡ y ∷ t
            → s ≡ t
equal-tails {𝓤} {X} refl = refl

[_] : {X : 𝓤 ̇ } → X → List X
[ x ] = x ∷ []

_++_ : {X : 𝓤 ̇ } → List X → List X → List X
[]      ++ t = t
(x ∷ s) ++ t = x ∷ (s ++ t)

infixr 4 _++_

[]-right-neutral : {X : 𝓤 ̇ } (s : List X) → s ≡ s ++ []
[]-right-neutral []      = refl
[]-right-neutral (x ∷ s) = ap (x ∷_) ([]-right-neutral s)

++-assoc : {X : 𝓤 ̇ } → associative (_++_ {𝓤} {X})
++-assoc []      t u = refl
++-assoc (x ∷ s) t u = ap (x ∷_) (++-assoc s t u)

\end{code}

We now construct the group freely generated by a set A. The set-hood
requirement is needed later only, and so we don't include it as an
assumption in the following anonymous module:

\begin{code}

module _ {𝓤 : Universe}
         {A : 𝓤 ̇ }
       where

 X : 𝓤 ̇
 X = 𝟚 × A

 _⁻ : X → X
 (n , a)⁻ = (complement n , a)

 inv-invol : (x : X) → (x ⁻)⁻ ≡ x
 inv-invol (n , a) = ap (_, a) (complement-involutive n)

\end{code}

We will quotient the following type FA to get the undelying type of
the free group:

\begin{code}

 FA : 𝓤 ̇
 FA = List X

 η : A → FA
 η a = [ ₀ , a ]

\end{code}

We will quotient by the equivalence relation generated by the
following reduction relation:

\begin{code}

 _▷_ : FA → FA → 𝓤 ̇
 s ▷ t = Σ u ꞉ FA , Σ v ꞉ FA , Σ x ꞉ X , (s ≡ u ++ [ x ] ++ [ x ⁻ ] ++ v)
                                       × (t ≡ u ++ v)

 infix 1 _▷_

 ∷-▷ : {s t : FA} (x : X) → s ▷ t → x ∷ s ▷ x ∷ t
 ∷-▷ x (u , v , y , p , q) = (x ∷ u) , v , y , ap (x ∷_) p , ap (x ∷_) q

\end{code}

The following is a lemma for the Church-Rosser property, proved by
induction on u₀ and u₁:

\begin{code}

 churros : (u₀ v₀ u₁ v₁ : FA) (x₀ x₁ : X)

         → u₀ ++  [ x₀ ] ++ [ x₀ ⁻ ] ++ v₀
         ≡ u₁ ++  [ x₁ ] ++ [ x₁ ⁻ ] ++ v₁

         → (u₀ ++ v₀ ≡ u₁ ++ v₁)
         + (Σ t ꞉ FA , (u₀ ++ v₀ ▷ t) × (u₁ ++ v₁ ▷ t))

 churros u₀ v₀ u₁ v₁ x₀ x₁ = f u₀ u₁
  where
   f : (u₀ u₁ : FA)
     → u₀ ++  [ x₀ ] ++ [ x₀ ⁻ ] ++ v₀ ≡ u₁ ++  [ x₁ ] ++ [ x₁ ⁻ ] ++ v₁
     → (u₀ ++ v₀ ≡ u₁ ++ v₁) + (Σ t ꞉ FA , (u₀ ++ v₀ ▷ t) × (u₁ ++ v₁ ▷ t))

   f [] [] p = inl γ
    where
     have : x₀ ∷ x₀ ⁻  ∷ v₀
          ≡ x₁ ∷ x₁ ⁻  ∷ v₁
     have = p

     γ : v₀ ≡ v₁
     γ = equal-tails (equal-tails p)

   f [] (y₁ ∷ []) p = inl γ
    where
     have : x₀ ∷ x₀ ⁻ ∷ v₀
          ≡ y₁ ∷ x₁   ∷ x₁ ⁻ ∷ v₁
     have = p

     q = x₁ ⁻    ≡⟨ ap _⁻ ((equal-heads (equal-tails p))⁻¹) ⟩
         (x₀ ⁻)⁻ ≡⟨ inv-invol x₀ ⟩
         x₀      ≡⟨ equal-heads p ⟩
         y₁      ∎

     γ : v₀ ≡ y₁ ∷ v₁
     γ = transport (λ - → v₀ ≡ - ∷ v₁) q (equal-tails (equal-tails p))

   f [] (y₁ ∷ z₁ ∷ u₁) p = inr γ
    where
     have : x₀ ∷ x₀ ⁻ ∷ v₀
          ≡ y₁ ∷ z₁   ∷ u₁ ++ [ x₁ ] ++ [ x₁ ⁻ ] ++ v₁
     have = p

     d' : u₁ ++ [ x₁ ] ++ [ x₁ ⁻ ] ++ v₁ ▷ u₁ ++ v₁
     d' = u₁ , v₁ , x₁ , refl , refl

     d : v₀ ▷ u₁ ++ v₁
     d = transport (_▷ u₁ ++ v₁) ((equal-tails (equal-tails p))⁻¹) d'

     q = y₁ ⁻ ≡⟨ (ap (_⁻) (equal-heads p)⁻¹) ⟩
         x₀ ⁻ ≡⟨ equal-heads (equal-tails p) ⟩
         z₁   ∎

     e' : y₁ ∷ y₁ ⁻ ∷ u₁ ++ v₁ ▷ u₁ ++ v₁
     e' = [] , (u₁ ++ v₁) , y₁ , refl , refl

     e : y₁ ∷ z₁ ∷ u₁ ++ v₁ ▷ u₁ ++ v₁
     e = transport (λ - → y₁ ∷ - ∷ u₁ ++ v₁ ▷ u₁ ++ v₁) q e'

     γ : Σ t ꞉ FA , (v₀ ▷ t) × (y₁ ∷ z₁ ∷ u₁ ++ v₁ ▷ t)
     γ = (u₁ ++ v₁) , d , e

   f (y₀ ∷ []) [] p = inl γ
    where
     have : y₀ ∷ x₀   ∷ x₀ ⁻ ∷ v₀
          ≡ x₁ ∷ x₁ ⁻ ∷ v₁
     have = p

     γ = y₀ ∷ v₀      ≡⟨ ap (_∷ v₀) (equal-heads p) ⟩
         x₁ ∷ v₀      ≡⟨ ap (_∷ v₀) ((inv-invol x₁)⁻¹) ⟩
         (x₁ ⁻)⁻ ∷ v₀ ≡⟨ ap (λ - → - ⁻ ∷ v₀) ((equal-heads (equal-tails p))⁻¹) ⟩
         x₀ ⁻ ∷ v₀    ≡⟨ equal-tails (equal-tails p) ⟩
         v₁           ∎

   f (y₀ ∷ z₀ ∷ u₀) [] p = inr γ
    where
     have : y₀ ∷ z₀   ∷ u₀ ++ [ x₀ ] ++ [ x₀ ⁻ ] ++ v₀
          ≡ x₁ ∷ x₁ ⁻ ∷ v₁
     have = p

     q = y₀ ⁻ ≡⟨ ap (_⁻) (equal-heads p) ⟩
         x₁ ⁻ ≡⟨ (equal-heads (equal-tails p))⁻¹ ⟩
         z₀   ∎

     d' : y₀ ∷ y₀ ⁻ ∷ u₀ ++ v₀ ▷ u₀ ++ v₀
     d' = [] , (u₀ ++ v₀) , y₀ , refl , refl

     d : y₀ ∷ z₀ ∷ u₀ ++ v₀ ▷ u₀ ++ v₀
     d = transport (λ - → y₀ ∷ - ∷ u₀ ++ v₀ ▷ u₀ ++ v₀) q d'

     e' : u₀ ++ [ x₀ ] ++ [ x₀ ⁻ ] ++ v₀ ▷ u₀ ++ v₀
     e' = u₀ , v₀ , x₀ , refl , refl

     e : v₁ ▷ u₀ ++ v₀
     e = transport (_▷ u₀ ++ v₀) (equal-tails (equal-tails p)) e'

     γ : Σ t ꞉ FA , (y₀ ∷ z₀ ∷ u₀ ++ v₀ ▷ t) × (v₁ ▷ t)
     γ = (u₀ ++ v₀) , d , e

   f (y₀ ∷ u₀) (y₁ ∷ u₁) p = γ
    where
     have : y₀ ∷ u₀ ++ [ x₀ ] ++ [ x₀ ⁻ ] ++ v₀
          ≡ y₁ ∷ u₁ ++ [ x₁ ] ++ [ x₁ ⁻ ] ++ v₁
     have = p

     IH : (u₀ ++ v₀ ≡ u₁ ++ v₁) + (Σ t ꞉ FA , (u₀ ++ v₀ ▷ t) × (u₁ ++ v₁ ▷ t))
     IH = f u₀ u₁ (equal-tails p)

     Γ : X → X → 𝓤 ̇
     Γ y₀ y₁ = (y₀ ∷ u₀ ++ v₀ ≡ y₁ ∷ u₁ ++ v₁)
             + (Σ t ꞉ FA , (y₀ ∷ u₀ ++ v₀ ▷ t) × (y₁ ∷ u₁ ++ v₁ ▷ t))

     δ : type-of IH → ∀ {y₀ y₁} → y₀ ≡ y₁ → Γ y₀ y₁
     δ (inl q)           {y₀} refl = inl (ap (y₀ ∷_) q)
     δ (inr (t , d , e)) {y₀} refl = inr ((y₀ ∷ t) , ∷-▷ y₀ d , ∷-▷ y₀ e)

     γ : Γ y₀ y₁
     γ = δ IH (equal-heads p)

 Church-Rosser : (s t₀ t₁ : FA)
               → s ▷ t₀
               → s ▷ t₁
               → (t₀ ≡ t₁) + (Σ t ꞉ FA , (t₀ ▷ t) × (t₁ ▷ t))
 Church-Rosser s t₀ t₁ (u₀ , v₀ , x₀ , p₀ , q₀) (u₁ , v₁ , x₁ , p₁ , q₁) = γ δ
  where
   δ : (u₀ ++ v₀ ≡ u₁ ++ v₁) + (Σ t ꞉ FA , (u₀ ++ v₀ ▷ t) × (u₁ ++ v₁ ▷ t))
   δ = churros u₀ v₀ u₁ v₁ x₀ x₁ (p₀ ⁻¹ ∙ p₁)

   γ : type-of δ → (t₀ ≡ t₁) + (Σ t ꞉ FA , (t₀ ▷ t) × (t₁ ▷ t))
   γ (inl q)           = inl (q₀ ∙ q ∙ q₁ ⁻¹)
   γ (inr (t , p , q)) = inr (t , transport (_▷ t) (q₀ ⁻¹) p ,
                                  transport (_▷ t) (q₁ ⁻¹) q)

\end{code}

The following import defines

  _◁▷_       the symmetric closure of _▷_,
  _∿_        the symmetric, reflexive, transitive closure of _▷_,
  _▷*_       the reflexive, transitive closure of _▷_,
  _▷[ n ]_   the n-fold iteration of _▷_.
  _◁▷[ n ]_  the n-fold iteration of _◁▷_.

\begin{code}

 open import SRTclosure
 open Church-Rosser _▷_

\end{code}

The insertion of generators is left cancellable before quotienting:

\begin{code}

 η-lc : {a b : A} → η a ≡ η b → a ≡ b
 η-lc refl = refl

\end{code}

The following will give that the insertion of generators is injective
after quotienting:

\begin{code}

 η-irreducible : {a : A} {s : FA} → ¬ (η a ▷ s)
 η-irreducible ((x ∷ []) , v , y , () , refl)
 η-irreducible ((x ∷ y ∷ u) , v , z , () , q)

 η-irreducible* : {a : A} {s : FA} → η a ▷* s → η a ≡ s
 η-irreducible* {a} {s} (n , r) = f n r
  where
   f : (n : ℕ) → η a ▷[ n ] s → η a ≡ s
   f zero     refl = refl
   f (succ n) (t , r , i) = 𝟘-elim (η-irreducible r)

 η-∿ : {a b : A} → η a ∿ η b → a ≡ b
 η-∿ {a} {b} e = η-lc p
  where
   σ : Σ s ꞉ FA , (η a ▷* s) × (η b ▷* s)
   σ = from-∿ Church-Rosser (η a) (η b) e
   s = pr₁ σ

   p = η a ≡⟨  η-irreducible* (pr₁ (pr₂ σ)) ⟩
       s   ≡⟨ (η-irreducible* (pr₂ (pr₂ σ)))⁻¹ ⟩
       η b ∎

\end{code}

We need to work with the truncation of _∿_ to construct the free
group, but most of the work will be done before truncation.

The following is for reasoning with chains of equivalences _∿_:

\begin{code}

 _∿⟨_⟩_ : (s : FA) {t u : FA} → s ∿ t → t ∿ u → s ∿ u
 _ ∿⟨ p ⟩ q = srt-transitive _▷_ _ _ _ p q

 _∿∎ : (s : FA) → s ∿ s
 _∿∎ _ = srt-reflexive _▷_ _

 infixr 0 _∿⟨_⟩_
 infix  1 _∿∎

\end{code}

The group operation before quotienting is simply concatenation.

Concatenation is a left congruence:

\begin{code}

 ++-▷-left : (s s' t : FA) → s ▷ s' → s ++ t ▷ s' ++ t
 ++-▷-left s s' t (u , v , x , p , q) = u , (v ++ t) , x , p' , q'
  where
   p' = s ++ t                            ≡⟨ ap (_++ t) p ⟩
        (u ++ [ x ] ++ [ x ⁻ ] ++ v) ++ t ≡⟨ ++-assoc u ([ x ] ++ [ x ⁻ ] ++ v) t ⟩
        u ++ [ x ] ++ [ x ⁻ ] ++ v ++ t   ∎

   q' = s' ++ t       ≡⟨ ap (_++ t) q ⟩
        (u ++ v) ++ t ≡⟨ ++-assoc u v t ⟩
        u ++ v ++ t   ∎

 ++-◁▷-left : (s s' t : FA) → s ◁▷ s' → s ++ t ◁▷ s' ++ t
 ++-◁▷-left s s' t (inl a) = inl (++-▷-left s s' t a)
 ++-◁▷-left s s' t (inr a) = inr (++-▷-left s' s t a)

 ++-iteration-left : (s s' t : FA) (n : ℕ)
                   → s ◁▷[ n ] s'
                   → s ++ t ◁▷[ n ] s' ++ t
 ++-iteration-left s s  t zero     refl        = refl
 ++-iteration-left s s' t (succ n) (u , b , c) = (u ++ t) ,
                                                 ++-◁▷-left s u t b ,
                                                 ++-iteration-left u s' t n c

 ++-cong-left : (s s' t : FA) → s ∿ s' → s ++ t ∿ s' ++ t
 ++-cong-left s s' t (n , a) = n , ++-iteration-left s s' t n a

\end{code}

It is also a right congruence:

\begin{code}

 ∷-◁▷ : (x : X) {s t : FA} → s ◁▷ t → x ∷ s ◁▷ x ∷ t
 ∷-◁▷ x (inl e) = inl (∷-▷ x e)
 ∷-◁▷ x (inr e) = inr (∷-▷ x e)

 ∷-iteration : (x : X) {s t : FA} (n : ℕ)
             → s ◁▷[ n ] t
             → x ∷ s ◁▷[ n ] x ∷ t
 ∷-iteration x zero refl = refl
 ∷-iteration x (succ n) (u , b , c) = (x ∷ u) , ∷-◁▷ x b , ∷-iteration x n c

 ∷-cong : (x : X) {s t : FA} → s ∿ t → x ∷ s ∿ x ∷ t
 ∷-cong x (n , a) = n , ∷-iteration x n a

 ++-cong-right : (s {t t'} : FA) → t ∿ t' → s ++ t ∿ s ++ t'
 ++-cong-right []      e = e
 ++-cong-right (x ∷ s) e = ∷-cong x (++-cong-right s e)

\end{code}

And therefore it is a two-sided congruence:

\begin{code}

 ++-cong-∿ : {s s' t t' : FA} → s ∿ s' → t ∿ t' → s ++ t ∿ s' ++ t'
 ++-cong-∿ {s} {s'} {t} {t'} d e = s ++ t   ∿⟨ ++-cong-left s s' t d ⟩
                                   s' ++ t  ∿⟨ ++-cong-right s' e ⟩
                                   s' ++ t' ∿∎
\end{code}

The group inverse, before quotienting:

\begin{code}

 inv : FA → FA
 inv [] = []
 inv (x ∷ s) = inv s ++ [ x ⁻ ]

\end{code}

It is a congruence:

\begin{code}

 inv-++ : (s t : FA) → inv (s ++ t) ≡ inv t ++ inv s
 inv-++ []      t = []-right-neutral (inv t)
 inv-++ (x ∷ s) t = inv (s ++ t) ++ [ x ⁻ ]     ≡⟨ IH ⟩
                    (inv t ++ inv s) ++ [ x ⁻ ] ≡⟨ assoc ⟩
                    inv t ++ (inv s ++ [ x ⁻ ]) ∎
  where
   IH    = ap (_++ [ x ⁻ ]) (inv-++ s t)
   assoc = ++-assoc (inv t) (inv s) [ x ⁻ ]

 inv-▷ : {s t : FA} → s ▷ t → inv s ▷ inv t
 inv-▷ {s} {t} (u , v , y , p , q) = inv v , inv u , y , p' , q'
  where
   p' = inv s                                     ≡⟨ I ⟩
        inv (u ++ [ y ] ++ [ y ⁻ ] ++ v)          ≡⟨ II ⟩
        inv ([ y ] ++ [ y ⁻ ] ++ v) ++ inv u      ≡⟨ III ⟩
        inv (([ y ] ++ [ y ⁻ ]) ++ v) ++ inv u    ≡⟨ IV ⟩
        (inv v ++ [ (y ⁻)⁻ ] ++ [ y ⁻ ]) ++ inv u ≡⟨ V ⟩
        (inv v ++ [ y ] ++ [ y ⁻ ]) ++ inv u      ≡⟨ VI ⟩
        inv v ++ [ y ] ++ [ y ⁻ ] ++ inv u        ∎
    where
     I   = ap inv p
     II  = inv-++ u ([ y ] ++ [ y ⁻ ] ++ v)
     III = ap (λ - → inv - ++ inv u) ((++-assoc [ y ] [ y ⁻ ] v)⁻¹)
     IV  = ap (_++ inv u) (inv-++ ([ y ] ++ [ y ⁻ ]) v)
     V   = ap (λ - → (inv v ++ [ - ] ++ [ y ⁻ ]) ++ inv u) (inv-invol y)
     VI  = ++-assoc (inv v) ([ y ] ++ [ y ⁻ ]) (inv u)

   q' = inv t          ≡⟨ ap inv q ⟩
        inv (u ++ v)   ≡⟨ inv-++ u v ⟩
        inv v ++ inv u ∎

 inv-◁▷ : {s t : FA} → s ◁▷ t → inv s ◁▷ inv t
 inv-◁▷ (inl e) = inl (inv-▷ e)
 inv-◁▷ (inr e) = inr (inv-▷ e)

 inv-iteration : {s t : FA} (n : ℕ)
               → s ◁▷[ n ] t
               → inv s ◁▷[ n ] inv t
 inv-iteration zero refl = refl
 inv-iteration (succ n) (u , b , c) = inv u , inv-◁▷ b , inv-iteration n c

 inv-cong-∿ : {s t : FA} → s ∿ t → inv s ∿ inv t
 inv-cong-∿ (n , a) = n , inv-iteration n a

\end{code}

The inverse really is an inverse:

\begin{code}

 =-∿ : {s s' : FA} → s ≡ s' → s ∿ s'
 =-∿ {s} refl = srt-reflexive _▷_ s

 inv-lemma : (x : X) → [ x ] ++ [ x ⁻ ] ∿ []
 inv-lemma x = srt-extension _▷_ _ [] ([] , [] , x , refl , refl)

 inv-lemma' : (x : X) → [ x ⁻ ] ++ [ x ] ∿ []
 inv-lemma' x = srt-extension _▷_ _ _
                 ([] ,
                  [] ,
                  (x ⁻) ,
                  ap (λ - → [ x ⁻ ] ++ [ - ]) ((inv-invol x)⁻¹) , refl)

 inv-property-∿ : (s : FA) → s ++ inv s ∿ []
 inv-property-∿ []      = srt-reflexive _▷_ []
 inv-property-∿ (x ∷ s) = γ
  where
   IH : s ++ inv s ∿ []
   IH = inv-property-∿ s

   γ = [ x ] ++ s ++ inv s ++ [ x ⁻ ]   ∿⟨ I ⟩
       [ x ] ++ (s ++ inv s) ++ [ x ⁻ ] ∿⟨ II ⟩
       [ x ] ++ [ x ⁻ ]                 ∿⟨ III ⟩
       []                               ∿∎
    where
     I   = =-∿  (ap (x ∷_) (++-assoc s (inv s) [ x ⁻ ])⁻¹)
     II  = ++-cong-right [ x ] (++-cong-left _ _ _ IH)
     III = inv-lemma x

 inv-property'-∿ : (s : FA) → inv s ++ s ∿ []
 inv-property'-∿ []      = srt-reflexive _▷_ []
 inv-property'-∿ (x ∷ s) = γ
  where
   γ = (inv s ++ [ x ⁻ ]) ++ (x ∷ s)    ∿⟨ I ⟩
       inv s ++ ([ x ⁻ ] ++ [ x ] ++ s) ∿⟨ II ⟩
       inv s ++ ([ x ⁻ ] ++ [ x ]) ++ s ∿⟨ III ⟩
       inv s ++ s                       ∿⟨ IV ⟩
       []                               ∿∎
    where
     I   = =-∿ (++-assoc (inv s) [ x ⁻ ] (x ∷ s))
     II  = =-∿ (ap (inv s ++_) ((++-assoc [ x ⁻ ] [ x ] s)⁻¹))
     III = ++-cong-right (inv s) (++-cong-left _ _ _ (inv-lemma' x))
     IV  = inv-property'-∿ s

\end{code}

The propositional, symmetric, reflexive, transitive closure of _▷_:

\begin{code}

 module _ (pt : propositional-truncations-exist) where

  open PropositionalTruncation pt

  _∾_ : FA → FA → 𝓤 ̇
  x ∾ y = ∥ x ∿ y ∥

  infix 1 _∾_

  η-∾ : {a b : A} → is-set A → η a ∾ η b → a ≡ b
  η-∾ i = ∥∥-rec i η-∿

  ++-cong : {s s' t t' : FA} → s ∾ s' → t ∾ t' → s ++ t ∾ s' ++ t'
  ++-cong = ∥∥-functor₂ ++-cong-∿

  inv-cong : {s t : FA} → s ∾ t → inv s ∾ inv t
  inv-cong = ∥∥-functor inv-cong-∿

  inv-right : (s : FA) → s ++ inv s ∾ []
  inv-right s = ∣ inv-property-∿ s ∣

  inv-left : (s : FA) → inv s ++ s ∾ []
  inv-left s = ∣ inv-property'-∿ s ∣

\end{code}

To perform the quotient, we assume functional and propositional
extensionality.

\begin{code}

  module _ (fe' : FunExt)
           (pe  : propext 𝓤)
        where

   fe : Fun-Ext
   fe {𝓤} {𝓥} = fe' 𝓤 𝓥

   open import UF-Quotient
   open Quotient 𝓤 𝓤 pt fe' pe
   open psrt pt _▷_

   R : EqRel FA
   R = _∾_ , psrt-is-prop-valued , psrt-reflexive , psrt-symmetric , psrt-transitive

\end{code}

Our quotients constructed via propositional truncation increase
universe levels (this won't be a problem for our intended application,
the free group over the type of ordinals, because although this type
is large, it is locally small):

\begin{code}

   FA/∾ : 𝓤 ⁺ ̇
   FA/∾ = FA / R

   η/∾ : FA → FA/∾
   η/∾ = η/ R

\end{code}

We have too many η's now. The insertion of generators is the following:

\begin{code}

   ηη : A → FA/∾
   ηη a = η/∾ (η a)

   ηη-lc : is-set A → (a b : A) → ηη a ≡ ηη b → a ≡ b
   ηη-lc i a b p = η-∾ i (η/-relates-identified-points R p)

   η/∾-identifies-related-points : {s t : FA} → s ∾ t → η/∾ s ≡ η/∾ t
   η/∾-identifies-related-points = η/-identifies-related-points R

\end{code}

We now need to make FA/∾ into a group. We will use "/" in names to
indicate constructions on the quotient FA/∾.

\begin{code}

   e/ : FA/∾
   e/ = η/∾ []

   inv/ : FA/∾ → FA/∾
   inv/ = extension₁/ R inv inv-cong

   _·_ : FA/∾ → FA/∾ → FA/∾
   _·_ = extension₂/ R _++_ ++-cong

   inv/-natural : (s : FA) → inv/ (η/∾ s) ≡ η/∾ (inv s)
   inv/-natural = naturality/ R inv inv-cong

   ·-natural : (s t : FA) → η/∾ s · η/∾ t ≡ η/∾ (s ++ t)
   ·-natural = naturality₂/ R _++_ ++-cong

   ln/ : left-neutral e/ _·_
   ln/ = /-induction R (λ x → e/ · x ≡ x) (λ x → quotient-is-set R) γ
    where
     γ : (s : FA) → η/∾ [] · η/∾ s ≡ η/∾ s
     γ = ·-natural []

   rn/ : right-neutral e/ _·_
   rn/ = /-induction R (λ x → x · e/ ≡ x) (λ x → quotient-is-set R) γ
    where
     γ : (s : FA) → η/∾ s · η/∾ [] ≡ η/∾ s
     γ s = η/∾ s · η/∾ [] ≡⟨ ·-natural s [] ⟩
           η/∾ (s ++ [])  ≡⟨ ap η/∾ ([]-right-neutral s ⁻¹) ⟩
           η/∾ s          ∎

   invl/ : (x : FA/∾) → inv/ x · x ≡ e/
   invl/ = /-induction R (λ x → (inv/ x · x) ≡ e/) (λ x → quotient-is-set R) γ
    where
     γ : (s : FA) → inv/ (η/∾ s) · η/∾ s ≡ e/
     γ s = inv/ (η/∾ s) · η/∾ s ≡⟨ ap (_· η/∾ s) (inv/-natural s) ⟩
           η/∾ (inv s) · η/∾ s  ≡⟨ ·-natural (inv s) s ⟩
           η/∾ (inv s ++ s)     ≡⟨ η/∾-identifies-related-points (inv-left s) ⟩
           η/∾ []               ≡⟨ refl ⟩
           e/                   ∎

   invr/ : (x : FA/∾) → x · inv/ x ≡ e/
   invr/ = /-induction R (λ x → x · inv/ x ≡ e/) (λ x → quotient-is-set R) γ
    where
     γ : (s : FA) → η/∾ s · inv/ (η/∾ s) ≡ e/
     γ s = η/∾ s · inv/ (η/∾ s) ≡⟨ ap (η/∾ s ·_) (inv/-natural s) ⟩
           η/∾ s · η/∾ (inv s)  ≡⟨ ·-natural s (inv s) ⟩
           η/∾ (s ++ inv s)     ≡⟨ η/∾-identifies-related-points (inv-right s) ⟩
           η/∾ []               ≡⟨ refl ⟩
           e/                   ∎

   assoc/ : associative _·_
   assoc/ = /-induction R (λ x → ∀ y z → (x · y) · z ≡ x · (y · z))
              (λ x → Π₂-is-prop fe (λ y z → quotient-is-set R))
              (λ s → /-induction R (λ y → ∀ z → (η/∾ s · y) · z ≡ η/∾ s · (y · z))
                       (λ y → Π-is-prop fe (λ z → quotient-is-set R))
                       (λ t → /-induction R (λ z → (η/∾ s · η/∾ t) · z ≡ η/∾ s · (η/∾ t · z))
                                (λ z → quotient-is-set R)
                                (γ s t)))
    where
     γ : (s t u : FA) → (η/∾ s · η/∾ t) · η/∾ u ≡ η/∾ s · (η/∾ t · η/∾ u)
     γ s t u = (η/∾ s · η/∾ t) · η/∾ u ≡⟨ ap (_· η/∾ u) (·-natural s t) ⟩
               η/∾ (s ++ t) · η/∾ u    ≡⟨ ·-natural (s ++ t) u ⟩
               η/∾ ((s ++ t) ++ u)     ≡⟨ ap η/∾ (++-assoc s t u) ⟩
               η/∾ (s ++ (t ++ u))     ≡⟨ (·-natural s (t ++ u))⁻¹ ⟩
               η/∾ s · η/∾ (t ++ u)    ≡⟨ ap (η/∾ s ·_) ((·-natural t u)⁻¹) ⟩
               η/∾ s · (η/∾ t · η/∾ u) ∎
\end{code}

So we have constructed a group with underlying set FA/∾ and a map ηη :
A → FA/∾.

To prove that ηη is the universal map of the set A into a group, we
assume another group G:

\begin{code}

   module _ {𝓥 : Universe}
            (G : 𝓥 ̇ )
            (G-is-set : is-set G)
            (e : G)
            (invg : G → G)
            (_⋆_ : G → G → G)
            (ln : left-neutral e _⋆_)
            (rn : right-neutral e _⋆_)
            (invl : (g : G) → invg g ⋆ g ≡ e)
            (invr : (g : G) → g ⋆ invg g ≡ e)
            (assoc : associative _⋆_)
            (f : A → G)
         where

    h : FA → G
    h [] = e
    h ((₀ , a) ∷ s) = f a ⋆ h s
    h ((₁ , a) ∷ s) = invg (f a) ⋆ h s

    h⁻ : (x : X) → h (x  ∷  x ⁻ ∷ []) ≡ e

    h⁻ (₀ , a) = f a ⋆ (invg (f a) ⋆ e)≡⟨ ap (f a ⋆_) (rn (invg (f a))) ⟩
                 f a ⋆ invg (f a)      ≡⟨ invr (f a) ⟩
                 e                     ∎

    h⁻ (₁ , a) = invg (f a) ⋆ (f a ⋆ e)≡⟨ ap (invg (f a) ⋆_) (rn (f a)) ⟩
                 invg (f a) ⋆ f a      ≡⟨ invl (f a) ⟩
                 e                     ∎

    h-is-hom : (s t : FA) → h (s ++ t) ≡ h s ⋆ h t

    h-is-hom [] t = h  t    ≡⟨ (ln (h t))⁻¹ ⟩
                    e ⋆ h t ∎

    h-is-hom ((₀ , a) ∷ s) t = f a ⋆ h (s ++ t)    ≡⟨ ap (f a ⋆_) (h-is-hom s t) ⟩
                               f a ⋆ (h s ⋆ h t)   ≡⟨ (assoc (f a) (h s) (h t))⁻¹ ⟩
                               (f a ⋆ h s) ⋆ h t   ≡⟨ refl ⟩
                               h (₀ , a ∷ s) ⋆ h t ∎

    h-is-hom (₁ , a ∷ s) t = invg (f a) ⋆ h (s ++ t)  ≡⟨ ap (invg (f a) ⋆_) (h-is-hom s t) ⟩
                             invg (f a) ⋆ (h s ⋆ h t) ≡⟨ (assoc (invg (f a)) (h s) (h t))⁻¹ ⟩
                             (invg (f a) ⋆ h s) ⋆ h t ≡⟨ refl ⟩
                             h (₁ , a ∷ s) ⋆ h t      ∎

    h-identifies-▷-related-points : {s t : FA} → s ▷ t → h s ≡ h t
    h-identifies-▷-related-points {s} {t} (u , v , y , p , q) =
       h s ≡⟨ ap h p ⟩
       h (u ++ [ y ] ++ [ y ⁻ ] ++ v)   ≡⟨ h-is-hom u ([ y ] ++ [ y ⁻ ] ++ v) ⟩
       h u ⋆ h (y ∷ y ⁻ ∷ v)            ≡⟨ ap (h u ⋆_) (h-is-hom (y ∷ y ⁻ ∷ []) v) ⟩
       h u ⋆ (h (y ∷ (y ⁻) ∷ []) ⋆ h v) ≡⟨ ap (λ - → h u ⋆ (- ⋆ h v)) (h⁻ y) ⟩
       h u ⋆ (e ⋆ h v)                  ≡⟨ ap (h u ⋆_) (ln (h v)) ⟩
       h u ⋆ h v                        ≡⟨ (h-is-hom u v)⁻¹ ⟩
       h (u ++ v)                       ≡⟨ ap h (q ⁻¹) ⟩
       h t ∎

    h-identifies-▷*-related-points : {s t : FA} → s ▷* t → h s ≡ h t
    h-identifies-▷*-related-points {s} {t} (n , r) = γ n s t r
     where
      γ : (n : ℕ) (s t : FA) → s ▷[ n ] t → h s ≡ h t
      γ zero s s refl  = refl
      γ (succ n) s t (u , r , i) = h s ≡⟨ h-identifies-▷-related-points r ⟩
                                   h u ≡⟨ γ n u t i ⟩
                                   h t ∎

    h-identifies-∾-related-points : {s t : FA} → s ∾ t → h s ≡ h t
    h-identifies-∾-related-points {s} {t} e = γ
     where
      δ : (Σ u ꞉ FA , (s ▷* u) × (t ▷* u)) → h s ≡ h t
      δ (u , σ , τ) = h s ≡⟨ (h-identifies-▷*-related-points σ) ⟩
                      h u ≡⟨ (h-identifies-▷*-related-points τ)⁻¹ ⟩
                      h t ∎
      γ : h s ≡ h t
      γ = ∥∥-rec G-is-set δ (∥∥-functor (from-∿ Church-Rosser s t) e)

\end{code}

We then construct the unique homorphism extending f using the
universal property of quotients:

\begin{code}


    f' : FA/∾ → G
    f' = mediating-map/ R G-is-set h h-identifies-∾-related-points

    f'-/triangle : f' ∘ η/∾ ∼ h
    f'-/triangle = universality-triangle/ R G-is-set h h-identifies-∾-related-points

\end{code}

And from this we get the triangle for the universal property of the
free group:

\begin{code}


    f'-triangle : f' ∘ ηη ∼ f
    f'-triangle a = f' (η/∾ (η a)) ≡⟨ f'-/triangle (η a) ⟩
                    h (η a)        ≡⟨ refl ⟩
                    f a ⋆ e        ≡⟨ rn (f a) ⟩
                    f a            ∎

    f'-is-hom : (x y : FA/∾) → f' (x · y) ≡ f' x ⋆ f' y
    f'-is-hom = /-induction R (λ x → ∀ y → f' (x · y) ≡ (f' x ⋆ f' y))
                  (λ x → Π-is-prop fe (λ y → G-is-set))
                  (λ s → /-induction R (λ y → f' (η/∾ s · y) ≡ (f' (η/∾ s) ⋆ f' y))
                           (λ a → G-is-set)
                           (γ s))
     where
      γ : (s t : FA) → f' (η/∾ s · η/∾ t) ≡ f' (η/∾ s) ⋆ f' (η/∾ t)
      γ s t = f' (η/∾ s · η/∾ t)      ≡⟨ ap f' (·-natural s t) ⟩
              f' (η/∾ (s ++ t))       ≡⟨ f'-/triangle (s ++ t) ⟩
              h (s ++ t)              ≡⟨ h-is-hom s t ⟩
              h s ⋆ h t               ≡⟨ ap₂ _⋆_ ((f'-/triangle s)⁻¹) ((f'-/triangle t)⁻¹) ⟩
              f' (η/∾ s) ⋆ f' (η/∾ t) ∎

    f'-uniqueness : (f₀ f₁ : FA/∾ → G) → f₀ ∘ η/∾ ∼ h → f₁ ∘ η/∾ ∼ h → f₀ ∼ f₁
    f'-uniqueness f₀ f₁ p q = at-most-one-mediating-map/ R G-is-set f₀ f₁
                                 (λ s → p s ∙ (q s)⁻¹)

\end{code}

What we wanted to know is now proved.

Last thing to do: Package the above into a single theorem, using a
type of groups, asserting the existence of free groups with injective
insertion of generators.
