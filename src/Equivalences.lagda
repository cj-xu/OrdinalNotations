-------------------------------------------------------------
- Three equivalent ordinal notation systems in Cubical Agda -
-------------------------------------------------------------

§3.4  Equivalences between the three approaches

We show that all our three approaches are equivalent in the strong
sense of Homotopy Type Theory.  To show A ≃ B, it suffices to
construct an isomorphism between A and B.  Hence we construct
isomorphisms between SigmaOrd and MutualOrd, and between MutualOrd
and HITOrd.

\begin{code}

{-# OPTIONS --cubical --safe #-}

module Equivalences where

open import Preliminaries
open import SigmaOrd   as S
open import MutualOrd  as M
open import HITOrd     as H

\end{code}

§3.4.1  SigmaOrd is equivalent to MutualOrd

■ From SigmaOrd to MutualOrd

\begin{code}

T2M : {a : Tree} → isCNF a → MutualOrd
T2M[<] : {a b : Tree} {p : isCNF a} {q : isCNF b}
       → a S.< b → T2M p M.< T2M q
T2M[≥fst] : {a b : Tree} {p : isCNF a} (q : isCNF b)
          → a S.≥ S.fst b → (T2M p) M.≥ M.fst (T2M q)
T2M[≡] : {a b : Tree} {p : isCNF a} {q : isCNF b}
       → a ≡ b → T2M p ≡ T2M q

T2M 𝟎IsCNF = 𝟎
T2M (ω^+IsCNF p q r) = ω^ T2M p + T2M q [ T2M[≥fst] q r ]

T2M[<] {_} {_} {𝟎IsCNF} {ω^+IsCNF _ _ _} <₁ = <₁
T2M[<] {_} {_} {ω^+IsCNF _ _ _} {ω^+IsCNF _ _ _} (<₂ r) = <₂ (T2M[<] r)
T2M[<] {_} {_} {ω^+IsCNF _ _ _} {ω^+IsCNF _ _ _} (<₃ e r) = <₃ (T2M[≡] e) (T2M[<] r)

T2M[≥fst] 𝟎IsCNF _ = M.≥𝟎
T2M[≥fst] (ω^+IsCNF _ _ _) (inj₁ r) = inj₁ (T2M[<] r)
T2M[≥fst] (ω^+IsCNF _ _ _) (inj₂ e) = inj₂ (T2M[≡] e)

import Agda.Builtin.Equality as P

T2M[≡] a=b with PropEqfromPath a=b
T2M[≡] a=b | P.refl = cong T2M (isCNFIsPropValued _ _)

S2M : SigmaOrd → MutualOrd
S2M (a , p) = T2M p

{-

We attempted to directly implement the function from SigmaOrd to
MutualOrd as follows:

----------------- Begin of code -----------------

S2M : SigmaOrd → MutualOrd
S2M[<] : {a b : SigmaOrd}
       → pr₁ a S.< pr₁ b → S2M a M.< S2M b
S2M[≥fst] : {a : SigmaOrd} (b : SigmaOrd)
          → (pr₁ a) S.≥ S.fst (pr₁ b) → (S2M a) M.≥ M.fst (S2M b)

S2M (𝟎 , 𝟎IsCNF) = 𝟎
S2M (ω^ a + b , ω^+IsCNF p q r) = ω^ S2M (a , p) + S2M (b , q) [ S2M[≥fst] (b , q) r ]

S2M[<] {_ , 𝟎IsCNF} {_ , ω^+IsCNF _ _ _} <₁ = <₁
S2M[<] {_ , ω^+IsCNF _ _ _} {_ , ω^+IsCNF _ _ _} (<₂ r) = <₂ (S2M[<] r)
S2M[<] {_ , ω^+IsCNF _ _ _} {_ , ω^+IsCNF _ _ _} (<₃ e r) = <₃ (cong S2M (SigmaOrd⁼ e)) (S2M[<] r)

S2M[≥fst] (_ , 𝟎IsCNF) _ = M.≥𝟎
S2M[≥fst] (_ , ω^+IsCNF _ _ _) (inj₁ r) = inj₁ (S2M[<] r)
S2M[≥fst] (_ , ω^+IsCNF _ _ _) (inj₂ e) = inj₂ (cong S2M (SigmaOrd⁼ e))

------------------ End of code ------------------

Agda then reports two termination errors:

1. The first one is caused by the paired argument of S2M and its
   lemmas, which is easily solved by currying them.

2. The other one is due to use of SigmaOrd⁼.  We solve it by
   simultaneously prove the curried equivalent T2M[≡] of SigmaOrd⁼
   specialized to the image of T2M, together with the trick of pattern
   matching on the Agda's propositional equality converted from the
   given path.

-}

\end{code}

■ From MutualOrd to SigmaOrd

\begin{code}

M2T : MutualOrd → Tree
M2T  𝟎               = 𝟎
M2T (ω^ a + b [ _ ]) = ω^ (M2T a) + (M2T b)

M2T[<] : {a b : MutualOrd}
       → a M.< b → M2T a S.< M2T b
M2T[<] <₁ = <₁
M2T[<] (<₂ r) = <₂ (M2T[<] r)
M2T[<] (<₃ e r) = <₃ (cong M2T e) (M2T[<] r)

M2T[≥fst] : {a : MutualOrd} (b : MutualOrd)
          → a M.≥ M.fst b → M2T a S.≥ S.fst (M2T b)
M2T[≥fst] 𝟎 r = S.≥𝟎
M2T[≥fst] (ω^ b + c [ r ]) (inj₁ a>b) = inj₁ (M2T[<] a>b)
M2T[≥fst] (ω^ b + c [ r ]) (inj₂ a=b) = inj₂ (cong M2T a=b)

isCNF[M2T] : (a : MutualOrd) → isCNF (M2T a)
isCNF[M2T] 𝟎 = 𝟎IsCNF
isCNF[M2T] (ω^ a + b [ r ]) =
 ω^+IsCNF (isCNF[M2T] a) (isCNF[M2T] b) (M2T[≥fst] b r)

M2S : MutualOrd → SigmaOrd
M2S a = (M2T a , isCNF[M2T] a)

\end{code}

■ Isomorphism between SigmaOrd and MutualOrd

\begin{code}

S2M2T=pr₁ : (a : SigmaOrd) → M2T (S2M a) ≡ pr₁ a
S2M2T=pr₁ (𝟎 , 𝟎IsCNF) = refl
S2M2T=pr₁ (ω^ a + b , ω^+IsCNF p q r) =
  cong₂ ω^_+_ (S2M2T=pr₁ (a , p)) (S2M2T=pr₁ (b , q))

S2M2S=id : (a : SigmaOrd) → M2S (S2M a) ≡ a
S2M2S=id a = SigmaOrd⁼ (S2M2T=pr₁ a)

M2S2M=id : (a : MutualOrd) → S2M (M2S a) ≡ a
M2S2M=id 𝟎 = refl
M2S2M=id (ω^ a + b [ _ ]) = MutualOrd⁼ (M2S2M=id a) (M2S2M=id b)

S≃M : SigmaOrd ≃ MutualOrd
S≃M = isoToEquiv (iso S2M M2S M2S2M=id S2M2S=id)

S≡M : SigmaOrd ≡ MutualOrd
S≡M = ua S≃M

\end{code}

§3.4.2  MutualOrd is equivalent to HITOrd

■ From MutualOrd to HITOrd

\begin{code}

M2H : MutualOrd → HITOrd
M2H 𝟎 = 𝟎
M2H (ω^ a + b [ _ ]) = ω^ M2H a ⊕ M2H b

\end{code}

■ From HITOrd to MutualOrd

\begin{code}

insert : MutualOrd → MutualOrd → MutualOrd
≥fst-insert : {a b : MutualOrd} (c : MutualOrd)
            → b M.≥ M.fst c → a M.< b
            → b M.≥ M.fst (insert a c)

insert a 𝟎 = ω^ a + 𝟎 [ M.≥𝟎 ]
insert a (ω^ b + c [ r ]) with <-tri a b
... | inj₁ a<b = ω^ b + insert a c [ ≥fst-insert c r a<b ]
... | inj₂ a≥b = ω^ a + ω^ b + c [ r ] [ a≥b ]

≥fst-insert {a} 𝟎 _ a<b = inj₁ a<b
≥fst-insert {a} (ω^ c + d [ _ ]) b≥c a<b with <-tri a c
... | inj₁ a<c = b≥c
... | inj₂ a≥c = inj₁ a<b

insert-swap : (x y z : MutualOrd)
            → insert x (insert y z) ≡ insert y (insert x z)
insert-swap x y 𝟎 with <-tri x y
insert-swap x y 𝟎 | inj₁ x<y with <-tri y x
insert-swap x y 𝟎 | inj₁ x<y | inj₁ y<x = ⊥-elim (Lm[<→¬≥] x<y (inj₁ y<x))
insert-swap x y 𝟎 | inj₁ x<y | inj₂ y≥x = MutualOrd⁼ refl (MutualOrd⁼ refl refl)
insert-swap x y 𝟎 | inj₂ x≥y with <-tri y x
insert-swap x y 𝟎 | inj₂ x≥y | inj₁ y<x = MutualOrd⁼ refl (MutualOrd⁼ refl refl)
insert-swap x y 𝟎 | inj₂ x≥y | inj₂ y≥x = MutualOrd⁼ (≤≥→≡ y≥x x≥y) (MutualOrd⁼ (≤≥→≡ x≥y y≥x) refl)
insert-swap x y (ω^ a + b [ _ ]) with <-tri y a
insert-swap x y (ω^ a + b [ _ ]) | inj₁ y<a with <-tri x a
insert-swap x y (ω^ a + b [ _ ]) | inj₁ y<a | inj₁ x<a with <-tri y a
insert-swap x y (ω^ a + b [ _ ]) | inj₁ y<a | inj₁ x<a | inj₁ y<a' = MutualOrd⁼ refl (insert-swap x y b)
insert-swap x y (ω^ a + b [ _ ]) | inj₁ y<a | inj₁ x<a | inj₂ y≥a  = ⊥-elim (Lm[<→¬≥] y<a y≥a)
insert-swap x y (ω^ a + b [ _ ]) | inj₁ y<a | inj₂ x≥a with <-tri y x
insert-swap x y (ω^ a + b [ _ ]) | inj₁ y<a | inj₂ x≥a | inj₁ y<x with <-tri y a
insert-swap x y (ω^ a + b [ _ ]) | inj₁ y<a | inj₂ x≥a | inj₁ y<x | inj₁ y<a' = MutualOrd⁼ refl (MutualOrd⁼ refl refl)
insert-swap x y (ω^ a + b [ _ ]) | inj₁ y<a | inj₂ x≥a | inj₁ y<x | inj₂ y≥a  = ⊥-elim (Lm[<→¬≥] y<a y≥a)
insert-swap x y (ω^ a + b [ _ ]) | inj₁ y<a | inj₂ x≥a | inj₂ y≥x = ⊥-elim (Lm[<→¬≥] y<a (≤-trans x≥a y≥x))
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a with <-tri x a
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₁ x<a with <-tri y a
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₁ x<a | inj₁ y<a  = ⊥-elim (Lm[<→¬≥] y<a y≥a)
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₁ x<a | inj₂ y≥a' with <-tri x y
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₁ x<a | inj₂ y≥a' | inj₁ x<y with <-tri x a
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₁ x<a | inj₂ y≥a' | inj₁ x<y | inj₁ x<a' = MutualOrd⁼ refl (MutualOrd⁼ refl refl)
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₁ x<a | inj₂ y≥a' | inj₁ x<y | inj₂ x≥a  = ⊥-elim (Lm[<→¬≥] x<a x≥a)
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₁ x<a | inj₂ y≥a' | inj₂ x≥y = ⊥-elim (Lm[<→¬≥] x<a (≤-trans y≥a x≥y))
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₂ x≥a with <-tri x y
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₂ x≥a | inj₁ x<y with <-tri x a
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₂ x≥a | inj₁ x<y | inj₁ x<a  = ⊥-elim (Lm[<→¬≥] x<a x≥a)
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₂ x≥a | inj₁ x<y | inj₂ x≥a' with <-tri y x
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₂ x≥a | inj₁ x<y | inj₂ x≥a' | inj₁ y<x = ⊥-elim (Lm[<→¬≥] x<y (inj₁ y<x))
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₂ x≥a | inj₁ x<y | inj₂ x≥a' | inj₂ y≥x = MutualOrd⁼ refl (MutualOrd⁼ refl refl)
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₂ x≥a | inj₂ x≥y with <-tri y x
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₂ x≥a | inj₂ x≥y | inj₁ y<x with <-tri y a
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₂ x≥a | inj₂ x≥y | inj₁ y<x | inj₁ y<a  = ⊥-elim (Lm[<→¬≥] y<a y≥a)
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₂ x≥a | inj₂ x≥y | inj₁ y<x | inj₂ y≥a' = MutualOrd⁼ refl (MutualOrd⁼ refl refl)
insert-swap x y (ω^ a + b [ _ ]) | inj₂ y≥a | inj₂ x≥a | inj₂ x≥y | inj₂ y≥x = MutualOrd⁼ (≤≥→≡ y≥x x≥y) (MutualOrd⁼ (≤≥→≡ x≥y y≥x) refl)

H2M : HITOrd → MutualOrd
H2M = rec MutualOrdIsSet 𝟎 insert insert-swap

\end{code}

■ Isomorphism between MutualOrd and HITOrd

\begin{code}

insert-+ : (a b : MutualOrd) (r : a M.≥ M.fst b)
         → insert a b ≡ ω^ a + b [ r ]
insert-+ a 𝟎 _ = MutualOrd⁼ refl refl
insert-+ a (ω^ b + c [ _ ]) a≥b with <-tri a b
... | inj₁ a<b  = ⊥-elim (Lm[<→¬≥] a<b a≥b)
... | inj₂ a≥b' = MutualOrd⁼ refl (MutualOrd⁼ refl refl)

M2H2M=id : (a : MutualOrd) → H2M (M2H a) ≡ a
M2H2M=id 𝟎 = refl
M2H2M=id ω^ a + b [ r ] = begin
    H2M (M2H ω^ a + b [ r ])
  ≡⟨ cong₂ insert (M2H2M=id a) (M2H2M=id b) ⟩
    insert a b
  ≡⟨ insert-+ a b r ⟩
    ω^ a + b [ r ]  ∎

insert-⊕ : (a b : MutualOrd)
         → M2H (insert a b) ≡ ω^ M2H a ⊕ M2H b
insert-⊕ a 𝟎 = refl
insert-⊕ a (ω^ b + c [ _ ]) with <-tri a b
... | inj₁ a<b = cong (ω^ M2H b ⊕_) (insert-⊕ a c) ∙ swap (M2H b) (M2H a) (M2H c)
... | inj₂ a≥b = refl

H2M2H=id : (a : HITOrd) → M2H (H2M a) ≡ a
H2M2H=id = indProp trunc base step
 where
  base : M2H (H2M 𝟎) ≡ 𝟎
  base = refl
  step : {x y : HITOrd}
       → M2H (H2M x) ≡ x → M2H (H2M y) ≡ y
       → M2H (H2M (ω^ x ⊕ y)) ≡ ω^ x ⊕ y
  step {x} {y} p q = begin
     M2H (H2M (ω^ x ⊕ y))
   ≡⟨ insert-⊕ (H2M x) (H2M y) ⟩
     ω^ M2H (H2M x) ⊕ M2H (H2M y)
   ≡⟨ cong₂ ω^_⊕_ p q ⟩
     ω^ x ⊕ y  ∎

M≃H : MutualOrd ≃ HITOrd
M≃H = isoToEquiv (iso M2H H2M H2M2H=id M2H2M=id)

M≡H : MutualOrd ≡ HITOrd
M≡H = ua M≃H

\end{code}
