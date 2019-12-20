-------------------------------------------------------------
- Three equivalent ordinal notation systems in Cubical Agda -
-------------------------------------------------------------

§3.3  The higher inductive approach

We consider finite multisets of ordinal representations, where the
order of elements does not matter.  Because the elements of the
multiset again are ordinal representations, we construct a higher
inductive type (HIT) of so-called hereditary multisets.

\begin{code}

{-# OPTIONS --cubical --safe #-}

module HITOrd where

open import Preliminaries

\end{code}

■ HIT of hereditary multisets

\begin{code}

infixr 40 ω^_⊕_

data HITOrd : Type₀ where
 𝟎 : HITOrd
 ω^_⊕_ : HITOrd → HITOrd → HITOrd
 swap : ∀ a b c → ω^ a ⊕ ω^ b ⊕ c ≡ ω^ b ⊕ ω^ a ⊕ c
 trunc : isSet HITOrd

private
 variable a b c : HITOrd

example : ω^ a ⊕ ω^ b ⊕ ω^ c ⊕ 𝟎 ≡ ω^ c ⊕ ω^ b ⊕ ω^ a ⊕ 𝟎
example {a} {b} {c} = begin
 ω^ a ⊕ ω^ b ⊕ ω^ c ⊕ 𝟎 ≡⟨ swap a b _ ⟩
 ω^ b ⊕ ω^ a ⊕ ω^ c ⊕ 𝟎 ≡⟨ cong (ω^ b ⊕_) (swap a c _) ⟩
 ω^ b ⊕ ω^ c ⊕ ω^ a ⊕ 𝟎 ≡⟨ swap b c _ ⟩
 ω^ c ⊕ ω^ b ⊕ ω^ a ⊕ 𝟎 ∎

\end{code}

■ Induction/elimination principles of HITOrd

\begin{code}

ind : (A : HITOrd → Type ℓ)
    → (a₀    : A 𝟎)
    → (_⋆_   : ∀ {x y} → A x → A y → A (ω^ x ⊕ y))
    → (⋆swap : ∀ {x y z} (a : A x) (b : A y) (c : A z)
             → PathP _ (a ⋆ (b ⋆ c)) (b ⋆ (a ⋆ c)))
    → (sv    : ∀ {x} → isSet (A x))
    → ∀ x → A x
ind A a₀ _⋆_ ⋆swap sv 𝟎 = a₀
ind A a₀ _⋆_ ⋆swap sv (ω^ x ⊕ y) =
  ind A a₀ _⋆_ ⋆swap sv x ⋆ ind A a₀ _⋆_ ⋆swap sv y
ind A a₀ _⋆_ ⋆swap sv (swap x y z i) =
  ⋆swap (ind A a₀ _⋆_ ⋆swap sv x)
        (ind A a₀ _⋆_ ⋆swap sv y)
        (ind A a₀ _⋆_ ⋆swap sv z) i
ind A a₀ _⋆_ ⋆swap sv (trunc p q i j) =
  isOfHLevel→isOfHLevelDep {n = 2}
                           (λ x a b → sv {x} {a} {b})
                           _ _
                           (cong (ind A a₀ _⋆_ ⋆swap sv) p)
                           (cong (ind A a₀ _⋆_ ⋆swap sv) q)
                           (trunc p q) i j

\end{code}

■ The recursion principle and the induction principle for propositions
  are just instances of the above full induction principle.

\begin{code}

rec : {A : Type ℓ}
    → isSet A
    → A
    → (_⋆_ : A → A → A)
    → (∀ x y z → x ⋆ (y ⋆ z) ≡ y ⋆ (x ⋆ z))
    → HITOrd → A
rec hset a₀ _⋆_ ⋆swap = ind _ a₀ _⋆_ ⋆swap hset

indProp : {P : HITOrd → Type ℓ}
        → (∀ {x} → isProp (P x))
        → P 𝟎
        → (∀ {x y} → P x → P y → P (ω^ x ⊕ y))
        → ∀ x → P x
indProp pv p₀ _⋆_ =
  ind _ p₀ _⋆_ (λ a b c → toPathP (pv _ _)) (isProp→isSet pv _ _)

\end{code}

■ Singleton multisets, representing the ω-based exponentiation

\begin{code}

ω^⟨_⟩ : HITOrd → HITOrd
ω^⟨ a ⟩ = ω^ a ⊕ 𝟎

𝟏 ω : HITOrd
𝟏 = ω^⟨ 𝟎 ⟩
ω = ω^⟨ 𝟏 ⟩

\end{code}
