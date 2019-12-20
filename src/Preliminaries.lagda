-------------------------------------------------------------
- Three equivalent ordinal notation systems in Cubical Agda -
-------------------------------------------------------------

§2  Cubical Agda

In the paper we give a brief introduction to Cubical Agda.

In this module, we import from the cubical library only what are needed
in our development.  We redefine some necessary data types because
using the standard library may cause problems in the cubical mode, and
the cubical library construct and name some data types differently from
those in the standard library.

\begin{code}

{-# OPTIONS --cubical --safe #-}

open import Agda.Primitive public
 using ( Level   -- universe levels
       ; lsuc    -- successor
       ; _⊔_     -- maximum
       )

open import Cubical.Foundations.Everything public
 using ( _∘_     -- function composition
       ; Type₀
       ; Type₁
       ; Type    -- universes, renamed from Set to Type
       ; ~_      -- interval reversal
       ; _∧_     -- interval minimum
       ; PathP   -- dependent cubical path
       ; _≡_     -- non-dependent path
       ; refl
       ; _⁻¹
       ; _∙_
       ; cong
       ; cong₂
       ; transp  -- generalized transport
       ; transport
       ; subst
       ; J
       ; lCancel -- p ∙ p ⁻¹ ≡ refl
       ; isOfHLevel→isOfHLevelDep
       ; isProp→isSet
       ; toPathP
       ; iso     -- constructor of isomorphism
       ; isoToEquiv
       ; ua      -- A ≃ B → A ≡ B
       )

open import Agda.Builtin.Cubical.Glue public
 using ( _≃_     -- equivalence
       )

open import Cubical.Data.Empty public
 using ( ⊥
       ; ⊥-elim
       )

open import Cubical.Relation.Nullary public
 using ( ¬_
       ; Dec
       ; yes
       ; no
       ; Discrete -- having decidable equality
       )

open import Cubical.Relation.Nullary.DecidableEq public
 using ( Discrete→isSet
       )

\end{code}

■ Generalizable variables of universe levels

\begin{code}

variable ℓ ℓ' ℓ'' : Level

\end{code}

■ Propositions and Sets

We redefine isSet to make the point arguments implicit.

\begin{code}
isProp isSet : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y
isSet A  = {x y : A} → isProp (x ≡ y)
\end{code}

■ Sums (disjoint unions)

We don't import it from the cubical library, because _⊎_ has the
default precedence which we prefer to make it much lower, and the
names of its constructors differ from those in Agda's standard library.

\begin{code}

infixr 2 _⊎_

data _⊎_ (A : Type ℓ) (B : Type ℓ') : Type (ℓ ⊔ ℓ') where
 inj₁ : A → A ⊎ B
 inj₂ : B → A ⊎ B

\end{code}

■ Σ-types (dependent pairs)

We find it more convenient to keep the first type argument implicit.

\begin{code}

infixr 1 _,_

record Σ {A : Type ℓ} (B : A → Type ℓ') : Set (ℓ ⊔ ℓ') where
 constructor _,_
 field
  pr₁ : A
  pr₂ : B pr₁

open Σ public

\end{code}

■ Cartesian products

\begin{code}

infixr 3 _×_

_×_ : Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
A × B = Σ \(_ : A) → B

\end{code}

■ Tools for equational reasoning

\begin{code}

infix  1 begin_
infixr 2 _≡⟨_⟩_
infix  3 _∎

private
 variable
  A : Type ℓ
  x y z : A

begin_ : x ≡ y → x ≡ y
begin x≡y = x≡y

_≡⟨_⟩_ : (x : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = x≡y ∙ y≡z

_∎ : (x : A) → x ≡ x
_ ∎ = refl

\end{code}

■ Inequality of natural numbers

\begin{code}

open import Agda.Builtin.Bool

open import Agda.Builtin.Nat public
  using (zero; suc)
  renaming (Nat to ℕ)

infix 10 _≤ᴺ_ _≥ᴺ_

data _≤ᴺ_ : ℕ → ℕ → Type₀ where
 z≤n : {n : ℕ} → 0 ≤ᴺ n
 s≤s : {n m : ℕ} → n ≤ᴺ m → suc n ≤ᴺ suc m

_≥ᴺ_ : ℕ → ℕ → Type₀
n ≥ᴺ m = m ≤ᴺ n

≤ᴺ-refl : {n : ℕ} → n ≤ᴺ n
≤ᴺ-refl {0}     = z≤n
≤ᴺ-refl {suc n} = s≤s ≤ᴺ-refl

n≤1+n : {n : ℕ} → n ≤ᴺ suc n
n≤1+n {0}     = z≤n
n≤1+n {suc n} = s≤s n≤1+n

\end{code}

■ Converting paths to Agda's propositional equality

Agda's termination checker sometimes is not happy with the cubical
"subst" function, such as in MutualOrd.lagda and Equivalences.lagda.
We please it by converting paths to Agda's propositional equality
which we can pattern match on directly.

\begin{code}

import Agda.Builtin.Equality as P

PropEqfromPath : {A : Set ℓ} {x y : A} → x ≡ y → x P.≡ y
PropEqfromPath {x = x} p = subst (x P.≡_) p P.refl

\end{code}
