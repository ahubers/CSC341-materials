open import Data.List
open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

module NatStringIso where

--------------------------------------------------------------------------------
-- This file is me playing around with a formal proof in Agda that ℕ and 0-1
-- strings are bijective (as you did informally in Lab 8B). In particular,
-- a few groups found a bijection that uses the binary encoding of the number, which
-- I was unable to falsify, which I have implemented. If I were smarter/less-lazy,
-- I could actually try to prove this encoding is a bijection.

--------------------------------------------------------------------------------
-- Binary representation of naturals.

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

b₀ =  ⟨⟩ O
b₁ = ⟨⟩ I
b₂ = ⟨⟩ I O
b₃ = ⟨⟩ I I
b₄ = ⟨⟩ I O

--------------------------------------------------------------------------------
-- Implementing encoding/decoding as repeated incrementation.

data Carry : Set where
  No : Carry
  Yes  : Carry

inc : Bin → Bin
inc b = go b Yes
  where
    go : Bin → Carry → Bin
    go ⟨⟩ No = ⟨⟩
    go ⟨⟩ Yes = ⟨⟩ I
    go (b O) No = (go b No) O
    go (b O) Yes = (go b No) I
    go (b I) No = (go b No) I
    go (b I) Yes = (go b Yes) O

-- Some tests
_ : inc (⟨⟩ I O O) ≡ ⟨⟩ I O I
_ = refl

_ : inc (⟨⟩ I I O) ≡ ⟨⟩ I I I
_ = refl

_ : inc (⟨⟩ I I I) ≡ ⟨⟩ I O O O
_ = refl
-- inc' : Bin → 

--------------------------------------------------------------------------------
-- Encoding & decoding.

encode : ℕ → Bin
encode zero = ⟨⟩ O
encode (suc n) = inc (encode n)

decode : Bin → ℕ
decode b = go b 0
  where
    go : Bin → ℕ → ℕ
    go ⟨⟩ n = 0
    go (b O) n = go b (n + 1)
    go (b I) n = 2 ^ n + go b (n + 1)

--------------------------------------------------------------------------------
-- Proof that encoding is half of an isomorphism.
--
-- Because of leading zeros, we know that encode ∘ decode ≠ ID.
-- However, we should have the other direction fine.

iso₁ : ∀ (n : ℕ) → decode (encode n) ≡ n
iso₁ zero = refl
iso₁ (suc n) = {!iso₁ n!} -- <---- Need to now reason about incrementation, but I'm lazy.

--------------------------------------------------------------------------------
-- Student encoding.

f : Bin → ℕ
f b = decode (_I b)
