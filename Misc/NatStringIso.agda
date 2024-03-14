open import Data.List
open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

module NatStringIso where

--------------------------------------------------------------------------------
-- This file is me playing around with a formal proof in Agda that ℕ and 0-1
-- strings are bijective (as you did informally in Lab 8B). In particular,
-- a few groups found a bijection that felt suspicious but I was unable to falsify.
-- So I have implemented it here. 
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
-- Student encoding.

-- Student solution is to take the binary encoding, prepend it with a 1,
-- and decode that to ℕ.

prepend-I : Bin → Bin
prepend-I ⟨⟩ = ⟨⟩ I
prepend-I (b O) = (prepend-I b) O
prepend-I (b I) = (prepend-I b) I

-- Student solution.
f : Bin → ℕ
f b = decode (prepend-I b)

unpend-I : Bin → Bin
unpend-I ⟨⟩ = ⟨⟩
unpend-I (⟨⟩ I) = ⟨⟩
unpend-I (b O) = (unpend-I b) O
unpend-I (b I) = (unpend-I b) I

g : ℕ → Bin
g n = unpend-I (encode n)

--------------------------------------------------------------------------------
-- If the encoding works, this should be a bijection.

iso₁ : ∀ (n : ℕ) → f (g n) ≡ (n + 2)
iso₁ zero = refl
iso₁ (suc n) = {!!}

iso₂ : ∀ (b : Bin) → g (f b) ≡ b
iso₂ ⟨⟩ = refl
iso₂ (b O) = {!!}
iso₂ (b I) = {!!}



