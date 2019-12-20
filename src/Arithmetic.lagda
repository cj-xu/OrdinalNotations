-------------------------------------------------------------
- Three equivalent ordinal notation systems in Cubical Agda -
-------------------------------------------------------------

§4  Ordinal arithmetic

As a case study, we construct the ordinary ordinal addition and
multiplication on MutualOrd and the Hessenberg addition and
multiplication on HITOrd, prove some of their properties, and then
transport the constructions and proofs between them.

\begin{code}

{-# OPTIONS --cubical --safe #-}

module Arithmetic where

open import Preliminaries
open import HITOrd as H
open import MutualOrd as M
open import Equivalences

infixr 35 _+_ _+ᴴ_ _⊕_ _⊕ᴹ_
infixr 36 _·_ _·ᴴ_ _⊗_ _⊗ᴹ_

Assoc : (A : Type₀) → (A → A → A) → Type₀
Assoc A _⋆_ = ∀ a b c → a ⋆ (b ⋆ c) ≡ (a ⋆ b) ⋆ c

Comm : (A : Type₀) → (A → A → A) → Type₀
Comm A _⋆_ = ∀ a b → a ⋆ b ≡ b ⋆ a

\end{code}

§4.1  Ordinary addition and multiplication

■ Ordinary addition on MutualOrd

\begin{code}

_+_ : MutualOrd → MutualOrd → MutualOrd
≥fst+ : {a : MutualOrd} (b c : MutualOrd)
      → a ≥ fst b → a ≥ fst c → a ≥ fst (b + c)

𝟎 + b = b
a + 𝟎 = a
(ω^ a + c [ r ]) + (ω^ b + d [ s ]) with <-tri a b
... | inj₁ a<b = ω^ b + d [ s ]
... | inj₂ a≥b = ω^ a + (c + ω^ b + d [ s ]) [ ≥fst+ c _ r a≥b ]

≥fst+ 𝟎 _ r s = s
≥fst+ (ω^ _ + _ [ _ ]) 𝟎 r s = r
≥fst+ (ω^ b + _ [ _ ]) (ω^ c + _ [ _ ]) r s with <-tri b c
... | inj₁ b<c = s
... | inj₂ b≥c = r

+unitl : (a : MutualOrd) → 𝟎 + a ≡ a
+unitl a = refl

+unitr : (a : MutualOrd) → a + 𝟎 ≡ a
+unitr 𝟎 = refl
+unitr ω^ a + b [ r ] = refl

+assoc : Assoc MutualOrd _+_
+assoc 𝟎 b c = refl
+assoc ω^ a + a' [ _ ] 𝟎 c = refl
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] 𝟎 = (+unitr _) ⁻¹
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] with <-tri a b | <-tri b c
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] | inj₁ a<b | inj₁ b<c with <-tri b c
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] | inj₁ a<b | inj₁ b<c | inj₁ _   with <-tri a c
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] | inj₁ a<b | inj₁ b<c | inj₁ _   | inj₁ _   = refl
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] | inj₁ a<b | inj₁ b<c | inj₁ _   | inj₂ a≥c = ⊥-elim (Lm[≥→¬<] a≥c (<-trans a<b b<c))
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] | inj₁ a<b | inj₁ b<c | inj₂ b≥c = ⊥-elim (Lm[≥→¬<] b≥c b<c)
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] | inj₁ a<b | inj₂ b≥c with <-tri a b
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] | inj₁ a<b | inj₂ b≥c | inj₁ _   with <-tri b c
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] | inj₁ a<b | inj₂ b≥c | inj₁ _   | inj₁ b<c = ⊥-elim (Lm[≥→¬<] b≥c b<c)
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] | inj₁ a<b | inj₂ b≥c | inj₁ _   | inj₂ _   = MutualOrd⁼ refl refl
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] | inj₁ a<b | inj₂ b≥c | inj₂ a≥b = ⊥-elim (Lm[≥→¬<] a≥b a<b)
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] | inj₂ a≥b | inj₁ b<c with <-tri a c
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] | inj₂ a≥b | inj₁ b<c | inj₁ a<c = refl
+assoc ω^ a + a' [ r ] ω^ b + b' [ s ] ω^ c + c' [ t ] | inj₂ a≥b | inj₁ b<c | inj₂ a≥c = MutualOrd⁼ refl (claim ∙ IH)
 where
  IH : a' + (ω^ b + b' [ s ] + ω^ c + c' [ t ]) ≡ (a' + ω^ b + b' [ s ]) + ω^ c + c' [ t ]
  IH = +assoc a' (ω^ b + b' [ s ]) (ω^ c + c' [ t ])
  fact : ω^ c + c' [ t ] ≡ ω^ b + b' [ s ] + ω^ c + c' [ t ]
  fact with <-tri b c
  fact | inj₁ _   = refl
  fact | inj₂ b≥c = ⊥-elim (Lm[≥→¬<] b≥c b<c)
  claim : a' + ω^ c + c' [ t ] ≡ a' + ω^ b + b' [ s ] + ω^ c + c' [ t ]
  claim = cong (a' +_) fact
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] | inj₂ a≥b | inj₂ b≥c with <-tri a b
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] | inj₂ a≥b | inj₂ b≥c | inj₁ a<b = ⊥-elim (Lm[≥→¬<] a≥b a<b)
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] | inj₂ a≥b | inj₂ b≥c | inj₂ _   with <-tri a c
+assoc ω^ a + a' [ _ ] ω^ b + b' [ _ ] ω^ c + c' [ _ ] | inj₂ a≥b | inj₂ b≥c | inj₂ _ | inj₁ a<c = ⊥-elim (Lm[≥→¬<] (≤-trans b≥c a≥b) a<c)
+assoc ω^ a + a' [ r ] ω^ b + b' [ s ] ω^ c + c' [ t ] | inj₂ a≥b | inj₂ b≥c | inj₂ _ | inj₂ a≥c = MutualOrd⁼ refl (claim ∙ IH)
 where
  fact : ω^ b + (b' + ω^ c + c' [ t ]) [ ≥fst+ b' _ s b≥c ] ≡ ω^ b + b' [ s ] + ω^ c + c' [ t ]
  fact with <-tri b c
  fact | inj₁ b<c = ⊥-elim (Lm[≥→¬<] b≥c b<c)
  fact | inj₂ _   = MutualOrd⁼ refl refl
  claim : a' + ω^ b + (b' + ω^ c + c' [ t ]) [ ≥fst+ b' _ s b≥c ] ≡ a' + ω^ b + b' [ s ] + ω^ c + c' [ t ]
  claim = cong (a' +_) fact
  IH : a' + ω^ b + b' [ s ] + ω^ c + c' [ t ] ≡ (a' + ω^ b + b' [ s ]) + ω^ c + c' [ t ]
  IH = +assoc a' (ω^ b + b' [ s ]) (ω^ c + c' [ t ])

b>0→a<a+b : ∀ a b → b > 𝟎 → a < a + b
b>0→a<a+b 𝟎 b r = r
b>0→a<a+b ω^ a + c [ r ] ω^ b + d [ s ] <₁ with <-tri a b
b>0→a<a+b ω^ a + c [ r ] ω^ b + d [ s ] <₁ | inj₁ a<b = <₂ a<b
b>0→a<a+b ω^ a + c [ r ] ω^ b + d [ s ] <₁ | inj₂ a≥b = <₃ refl (b>0→a<a+b c _ <₁)

a≤a+b : ∀ a b → a ≤ a + b
a≤a+b a 𝟎 = inj₂ (+unitr a)
a≤a+b a ω^ b + c [ r ] = inj₁ (b>0→a<a+b a _ <₁)

b≤a+b : ∀ a b → b ≤ a + b
b≤a+b a 𝟎 = ≥𝟎
b≤a+b 𝟎 ω^ b + d [ _ ] = inj₂ refl
b≤a+b ω^ a + c [ _ ] ω^ b + d [ _ ] with <-tri a b
b≤a+b ω^ a + c [ _ ] ω^ b + d [ _ ] | inj₁ a<b = inj₂ refl
b≤a+b ω^ a + c [ _ ] ω^ b + d [ _ ] | inj₂ (inj₁ a>b) = inj₁ (<₂ a>b)
b≤a+b ω^ a + c [ r ] ω^ b + d [ s ] | inj₂ (inj₂ a≡b) = inj₁ (<₃ (a≡b ⁻¹) (<≤-trans fact IH))
 where
  IH : ω^ b + d [ s ] ≤ c + ω^ b + d [ s ]
  IH = b≤a+b c (ω^ b + d [ s ])
  fact : d < ω^ b + d [ s ]
  fact = rest< b d s

-- Ordinals of the form ω^⟨ c ⟩ are closed under addition

additive-principal : {a b : MutualOrd}
                   → a < M.ω^⟨ b ⟩ → (a + M.ω^⟨ b ⟩) ≡ M.ω^⟨ b ⟩
additive-principal <₁ = refl
additive-principal {ω^ a + _ [ _ ]} {b} (<₂ a<b) with <-tri a b
... | inj₁ a<b' = refl
... | inj₂ a≥b  = ⊥-elim (Lm[≥→¬<] a≥b a<b)

additive-principal-closure : {a b c : MutualOrd}
                           → a < M.ω^⟨ c ⟩ → b < M.ω^⟨ c ⟩
                           → (a + b) < M.ω^⟨ c ⟩
additive-principal-closure <₁ q = q
additive-principal-closure (<₂ p) <₁ = <₂ p
additive-principal-closure {a} {b} (<₂ p) (<₂ q) with <-tri (fst a) (fst b)
... | inj₁ a<b = <₂ q
... | inj₂ a≥b = <₂ p

\end{code}

■ Ordinary addition on HITOrd

\begin{code}

_+ᴴ_ : HITOrd → HITOrd → HITOrd
_+ᴴ_ = transport (λ i → M≡H i → M≡H i → M≡H i) _+_

+Path : PathP (λ i → M≡H i → M≡H i → M≡H i) _+_ _+ᴴ_
+Path i = transp (λ j → M≡H (i ∧ j) → M≡H (i ∧ j) → M≡H (i ∧ j))
                 (~ i) _+_

+ᴴassoc : Assoc HITOrd _+ᴴ_
+ᴴassoc = transport (λ i → Assoc (M≡H i) (+Path i)) +assoc

\end{code}

■ Ordinary multiplication

\begin{code}

_·_ : MutualOrd → MutualOrd → MutualOrd
𝟎 · b = 𝟎
a · 𝟎 = 𝟎
a · (ω^ 𝟎 + d [ r ]) = a + a · d
(ω^ a + c [ r ]) · (ω^ b + d [ s ]) = M.ω^⟨ a + b ⟩ + (ω^ a + c [ r ] · d)

_·ᴴ_ : HITOrd → HITOrd → HITOrd
_·ᴴ_ = transport (λ i → M≡H i → M≡H i → M≡H i) _·_

\end{code}

■ Examples of computation

\begin{code}

-- _+_ and _·_ are not commutative.

Ex[+NonComm] :  M.𝟏 + M.ω  ≡ M.ω
             ×  M.ω + M.𝟏  > M.ω
Ex[+NonComm] = (refl , <₃ refl <₁)

Ex[·NonComm] :  (M.𝟏 + M.𝟏) · M.ω  ≡ M.ω
             ×  M.ω                < M.ω + M.ω
             ×  M.ω + M.ω          ≡ M.ω · (M.𝟏 + M.𝟏)
Ex[·NonComm] = (refl , <₃ refl <₁ , refl)

-- The transported operations _+ᴴ_ and _·ᴴ_ compute.

Ex[+ᴴComp] : H.𝟏 +ᴴ H.ω ≡ ω^ (ω^ 𝟎 ⊕ 𝟎) ⊕ 𝟎
Ex[+ᴴComp] = refl

Ex[·ᴴComp] : H.ω ·ᴴ (H.𝟏 +ᴴ H.𝟏)
           ≡ ω^ (ω^ 𝟎 ⊕ 𝟎) ⊕ ω^ (ω^ 𝟎 ⊕ 𝟎) ⊕ 𝟎
Ex[·ᴴComp] = refl

\end{code}

§4.2  Hessenberg addition and multiplication

■ Hessenberg addition on HITOrd

\begin{code}

_⊕_ : HITOrd → HITOrd → HITOrd
𝟎 ⊕ y = y
(ω^ a ⊕ b) ⊕ y = ω^ a ⊕ (b ⊕ y)
(swap a b c i) ⊕ y = swap a b (c ⊕ y) i
(trunc p q i j) ⊕ y = trunc (cong (λ x → x ⊕ y) p)
                             (cong (λ x → x ⊕ y) q)
                             i j

⊕unitl : (a : HITOrd) → 𝟎 ⊕ a ≡ a
⊕unitl a = refl

⊕unitr : (a : HITOrd) → a ⊕ 𝟎 ≡ a
⊕unitr = indProp trunc base step
 where
  base : 𝟎 ⊕ 𝟎 ≡ 𝟎
  base = refl
  step : ∀ {x y} → _ → y ⊕ 𝟎 ≡ y
       → (ω^ x ⊕ y) ⊕ 𝟎 ≡ ω^ x ⊕ y
  step {x} _ = cong (ω^ x ⊕_)

⊕assoc : Assoc HITOrd _⊕_
⊕assoc = indProp (λ {a} → hprop a) base (λ {x} {y} → step x y)
 where
  P : HITOrd → Type₀
  P a = ∀ b c → a ⊕ b ⊕ c ≡ (a ⊕ b) ⊕ c
  hprop : ∀ a → isProp (P a)
  hprop _ p q i b c = trunc (p b c) (q b c) i
  base : P 𝟎
  base _ _ = refl
  step : ∀ x y → P x → P y → P (ω^ x ⊕ y)
  step x y _ p b c = cong (ω^ x ⊕_) (p b c)

ω^⊕=⊕ω^ : (a b : HITOrd) → (ω^ a ⊕ b) ≡ b ⊕ H.ω^⟨ a ⟩
ω^⊕=⊕ω^ a = indProp trunc base step
 where
  P : HITOrd → Type₀
  P b = (ω^ a ⊕ b) ≡ b ⊕ H.ω^⟨ a ⟩
  base : P 𝟎
  base = refl
  step : ∀ {x y} → P x → P y → P (ω^ x ⊕ y)
  step {x} {y} _ p = swap a x y ∙ cong (ω^ x ⊕_) p

⊕comm : Comm HITOrd _⊕_
⊕comm a = indProp trunc base step
 where
  P : HITOrd → Type₀
  P b = a ⊕ b ≡ b ⊕ a
  base : P 𝟎
  base = ⊕unitr a
  step : ∀ {x y} → P x → P y → P (ω^ x ⊕ y)
  step {x} {y} _ p = begin
      a ⊕ (ω^ x ⊕ y)
    ≡⟨ cong (a ⊕_) (ω^⊕=⊕ω^ x y) ⟩
      a ⊕ (y ⊕ H.ω^⟨ x ⟩)
    ≡⟨ ⊕assoc a y H.ω^⟨ x ⟩ ⟩
      (a ⊕ y) ⊕ H.ω^⟨ x ⟩
    ≡⟨ cong (_⊕ H.ω^⟨ x ⟩) p ⟩
      (y ⊕ a) ⊕ H.ω^⟨ x ⟩
    ≡⟨ (ω^⊕=⊕ω^ x (y ⊕ a)) ⁻¹ ⟩
      (ω^ x ⊕ y) ⊕ a  ∎

\end{code}

■ Hessenberg addition on MutualOrd

\begin{code}

H≡M : HITOrd ≡ MutualOrd
H≡M i = M≡H (~ i)

_⊕ᴹ_ : MutualOrd → MutualOrd → MutualOrd
_⊕ᴹ_ = transport (λ i → H≡M i → H≡M i → H≡M i) _⊕_

⊕Path : PathP (λ i → H≡M i → H≡M i → H≡M i) _⊕_ _⊕ᴹ_
⊕Path i = transp (λ j → H≡M (i ∧ j) → H≡M (i ∧ j) → H≡M (i ∧ j)) (~ i) _⊕_

M⊕comm : Comm MutualOrd _⊕ᴹ_
M⊕comm = transport (λ i → Comm (H≡M i) (⊕Path i)) ⊕comm

\end{code}

■ Hessenberg multiplication

\begin{code}

_∔_ : HITOrd → HITOrd → HITOrd
𝟎 ∔ b = 𝟎
(ω^ a ⊕ c) ∔ b = ω^ (a ⊕ b) ⊕ (c ∔ b)
(swap x y z i) ∔ b = swap (x ⊕ b) (y ⊕ b) (z ∔ b) i
(trunc p q i j) ∔ b = trunc (cong (_∔ b) p) (cong (_∔ b) q) i j

⊕swap : ∀ a b c → a ⊕ b ⊕ c ≡ b ⊕ a ⊕ c
⊕swap a b c = begin
  a ⊕ (b ⊕ c) ≡⟨ ⊕assoc a b c ⟩
  (a ⊕ b) ⊕ c ≡⟨ cong (_⊕ c) (⊕comm a b) ⟩
  (b ⊕ a) ⊕ c ≡⟨ (⊕assoc b a c)⁻¹ ⟩
  b ⊕ (a ⊕ c) ∎

_⊗_ : HITOrd → HITOrd → HITOrd
a ⊗ 𝟎 = 𝟎
a ⊗ (ω^ b ⊕ c) = (a ∔ b) ⊕ (a ⊗ c)
a ⊗ (swap x y z i) = ⊕swap (a ∔ x) (a ∔ y) (a ⊗ z) i
a ⊗ (trunc p q i j) = trunc (cong (a ⊗_) p) (cong (a ⊗_) q) i j

_⊗ᴹ_ : MutualOrd → MutualOrd → MutualOrd
_⊗ᴹ_ = transport (λ i → H≡M i → H≡M i → H≡M i) _⊗_

\end{code}

■ Examples of computation

\begin{code}

-- Hessenberg addition is concatenation

Ex[⊕concat] :
   H.𝟏 ⊕ H.ω^⟨ H.ω ⟩ ⊕ H.ω
 ≡ ω^ 𝟎 ⊕ ω^ (ω^ (ω^ 𝟎 ⊕ 𝟎) ⊕ 𝟎) ⊕ ω^ (ω^ 𝟎 ⊕ 𝟎) ⊕ 𝟎
Ex[⊕concat] = refl

-- The transported operations _⊕ᴹ_ and _⊗ᴹ_ compute

Ex[⊕ᴹComp] : M.𝟏 ⊕ᴹ M.ω ≡ M.ω + M.𝟏
Ex[⊕ᴹComp] = refl

Ex[⊗ᴹComp] : (M.𝟏 + M.𝟏) ⊗ᴹ M.ω ≡ M.ω + M.ω
Ex[⊗ᴹComp] = refl

\end{code}
