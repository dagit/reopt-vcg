/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich

Basic operations on bitvectors.

This is a work-in-progress, and contains additions to other theories.
-/
import data.vector

import .common -- for dec_trivial_tac

@[reducible] def bitvec (sz:ℕ) :=
  { x : ℕ // x < (2 ^ sz) }

namespace bitvec
open nat
open vector

-- Create a zero bitvector
@[reducible] protected
def zero (n : ℕ) : bitvec n :=
  ⟨0, nat.pos_pow_of_pos n dec_trivial⟩

instance {n:ℕ} : has_zero (bitvec n) := ⟨bitvec.zero n⟩

-- Create a bitvector with the constant one.
@[reducible] protected
def one_of_pos_len (n: ℕ) {H : n > 0} : bitvec n :=
  ⟨1, calc
        1   < 2   : by dec_trivial_tac
        ... = 2^1 : by trivial
        ... ≤ 2^n : by apply (pow_le_pow_of_le_right (zero_lt_succ _) (succ_le_of_lt H))⟩

@[reducible] protected
def one (n:ℕ) : bitvec n :=
  begin
    cases n,
    case nat.zero
    -- Treating the zero length "one" bit vector as 0 simplifies
    -- other things, so we intentionally allow this special case.
    { apply bitvec.zero },
    case nat.succ
    { apply bitvec.one_of_pos_len, apply zero_lt_succ }
  end

instance {n:ℕ} : has_one (bitvec n)  := ⟨bitvec.one n⟩

protected def cong {a b : ℕ} (h : a = b) : bitvec a → bitvec b
| ⟨x, p⟩ := ⟨x, h ▸ p⟩

lemma in_range (x n : ℕ) : x % 2 ^ n < 2 ^ n :=
  begin
    apply (mod_lt _),
    apply (pos_pow_of_pos _ _),
    simp [zero_lt_succ]
  end

-- bitvec specific version of vector.append
def append {m n} (x: bitvec m) (y: bitvec n) : bitvec (m + n) := ⟨ (x.val * 2^n + y.val) % 2^(m + n), by simp [in_range] ⟩

lemma div_lt_of_lt_mul {m n : ℕ} : ∀ {k} (Hk : k > 0), m < k * n → m / k < n
  | 0        Hk h := by apply absurd Hk (lt_irrefl 0)
  | (succ k) Hk h :=
    suffices succ k * (m / succ k) < succ k * n, from lt_of_mul_lt_mul_left this (zero_le _),
    calc
      succ k * (m / succ k) ≤ m % succ k + succ k * (m / succ k) : le_add_left _ _
                        ... = m                                  : by rw mod_add_div
                        ... < succ k * n                         : h

lemma pow_mul {b n m :ℕ} : b^n * b^m = b^(n+m) :=
  begin
    induction m with m,
    case nat.zero
    { simp },
    case nat.succ
    { rw [pow_succ, ←mul_assoc (b^n), m_ih, ←pow_succ] }
  end

lemma sub_lt_left {a b} (c:ℕ) (H: a < b) (Ha: a > c) : a - c < b - c :=
  begin
    have Hb : b > c, { apply lt_trans Ha H },
    induction c with c generalizing a b,
    case nat.zero
    { rwa nat.sub_zero },
    case nat.succ
    { have a_gt : a > c, { apply lt_of_succ_lt Ha},
      have b_gt : b > c, { apply lt_of_succ_lt Hb},
      cases a,
      { simp at Ha,
        have : false, { apply not_lt_zero _ a_gt },
        contradiction,
      },
      cases b,
      { simp at Hb,
        have : false, { apply not_lt_zero _ b_gt },
        contradiction,
      },
      simp,
      apply c_ih (lt_of_succ_lt_succ H) (lt_of_succ_lt_succ Ha) (lt_of_succ_lt_succ Hb),
    }
  end

lemma sub_add_lt_self (a b c : ℕ) (Hab: a > b) (Hbc : b > c) : a - b + c < a :=
  begin
    induction c with c generalizing a b,
    case nat.zero
    { apply sub_lt_of_pos_le _ _ Hbc (le_of_lt Hab) },
    { cases b,
      case nat.zero
      { have : false, { apply not_lt_zero _ Hbc},
        contradiction,
      },
      { cases a,
        case nat.zero
        { have : false, { apply not_lt_zero _ Hab },
          contradiction,
        },
        case nat.succ
        { have Hbc: b > c, { apply lt_of_succ_lt_succ Hbc },
          have Hab: a > b, { apply lt_of_succ_lt_succ Hab },
          have := c_ih _ _ Hab Hbc,
          simp,
          rw [nat.add_comm],
          apply succ_lt_succ this,
        }
      },
    },
  end

section shift
  variable {n : ℕ}

  @[reducible]
  def shl (x : bitvec n) (i : ℕ) : bitvec n := ⟨x.val * 2^i % 2^n, by simp [in_range]⟩

  @[reducible]
  def lsb (x: bitvec n) : bool := x.val % 2 = 1

  -- unsigned shift right
  @[reducible]
  def ushr (x : bitvec n) (i : ℕ) : bitvec n := ⟨x.val / 2^i,
    calc
        x.val / 2^i ≤ x.val : by apply nat.div_le_self
                ... < 2^n   : by exact x.property⟩

  @[reducible]
  def msb (x: bitvec n) : bool := (ushr x (n-1)).val = 1

  -- signed shift right
  @[reducible]
  def sshr (x: bitvec n) (i:ℕ) : bitvec n :=
    -- When the sign bit is set in x, (msb x = 1), then we would like
    -- the result of sshr x i, to have the top i bits set.
    -- We can calculate a number that will do this in steps:
    -- 1) (2 ^ n) - 1, will have all the bits set.
    -- 2) (2 ^ (n-i)) - 1, will be a number with the lower (n-i) bits set.
    -- 3) subtract the previous two numbers (1) - (2), to get a
    -- number where only the top i bits are set.
    let upper_bits := 2 ^ n - 2 ^ (n-i) in
    let sign := if msb x then upper_bits else 0 in
    ⟨ sign + (ushr x i).val,
      begin
        simp [sign],
        cases (msb x),
        case bool.ff
        { simp [ushr],
          calc
            x.val / 2^i ≤ x.val : by apply nat.div_le_self
                    ... < 2^n   : x.property
        },
        case bool.tt
        { simp [upper_bits, sign, ushr],
          by_cases this : n ≤ i,
          { rw nat.sub_eq_zero_of_le this,
            simp,
            rw div_eq_of_lt,
            simp,
            apply sub_lt_of_pos_le,
            dec_trivial_tac,
            apply pos_pow_of_pos,
            dec_trivial_tac,
            calc
              x.val < 2^n : x.property
                ... ≤ 2^i : pow_le_pow_of_le_right (by dec_trivial_tac) this
          },
          { cases i, -- This is slightly annoying, but we need to prove
                     -- the i = 0 case separately so we can use i > 0
                     -- for sub_lt_of_pos_le as the argument to
                     -- pow_lt_pow_of_lt_right in the other case.
            -- case nat.zero
            { simp, rw nat.sub_self (2^n), simp, exact x.property },
            -- case nat.succ
            { have i_lt_n : succ i ≤ n,
              { apply le_of_not_ge this },
              have : x.val/2^succ i < 2^(n-succ i),
              { apply div_lt_of_lt_mul,
                apply pos_pow_of_pos,
                dec_trivial_tac,
                rw [pow_mul, add_sub_of_le],
                apply x.property,
                apply i_lt_n
              },
              apply sub_add_lt_self (2^n) (2^(n-succ i)) (x.val/2^(succ i)) _ this,
              apply pow_lt_pow_of_lt_right (lt_succ_self _)
                                           (sub_lt_of_pos_le _ _ (nat.zero_lt_succ i) i_lt_n)
            }
          }
        }
      end⟩

end shift

section bitwise

  -- A fixed width version of nat.bitwise
  -- This applies `f` to each bit in tthe vectors.
  def fin_bitwise (f: bool → bool → bool) : ℕ → ℕ → ℕ → ℕ
    | 0 _  _:= 0
    | (nat.succ w) x y :=
      let xr := x.bodd_div2 in
      let yr := y.bodd_div2 in
      nat.bit (f xr.fst yr.fst) (fin_bitwise w xr.snd yr.snd)

  -- A theorem that nat.bit is less than a power of two, when the input
  -- is.
  --
  -- The implicit parameters are chosen so that apply is useful here.
  theorem bit_lt_pow2  {w:ℕ} {b : bool} {x : ℕ} (h : x < 2^w)
  : nat.bit b x < 2^(w+1) :=
  begin
    -- Simplify 2^(w+1)
    simp [nat.add_succ, nat.pow_succ, nat.mul_comm _ 2, eq.symm (nat.bit0_val _)],
    -- Split on b and simplify bit
    cases b; simp [bit],
    case ff { apply nat.bit0_lt h, },
    case tt { apply nat.bit1_lt_bit0 h, }
  end

  theorem bitwise_lt (f: bool → bool → bool) (w:ℕ)
  : ∀(x y : ℕ),  fin_bitwise f w x y < 2^w :=
  begin
    induction w with w p,
    { intros, dec_trivial_tac, },
    intros,
    unfold fin_bitwise,
    apply bit_lt_pow2 (p _ _),
  end

  @[reducible]
  def bitwise {w:ℕ} (f: bool → bool → bool) (x y : bitvec w) : bitvec w :=
    ⟨fin_bitwise f w x.val y.val, bitwise_lt _ _ _ _⟩

  @[reducible]
  def not {w:ℕ} (x: bitvec w) : bitvec w := ⟨2^w - x.val - 1,
    begin
      have xval_pos : 0 < x.val + 1,
      { apply (succ_pos x.val) },
      apply (sub_lt _ xval_pos),
      apply pos_pow_of_pos,
      apply (succ_pos 1)
    end⟩

  @[reducible]
  def and {w:ℕ} : bitvec w → bitvec w → bitvec w := bitwise band
  @[reducible]
  def or  {w:ℕ} : bitvec w → bitvec w → bitvec w := bitwise bor
  @[reducible]
  def xor {w:ℕ} : bitvec w → bitvec w → bitvec w := bitwise bxor

end bitwise

section arith
  variable {n : ℕ}

  @[reducible]
  protected def neg (x : bitvec n) : bitvec n :=
    ⟨if x.val = 0 then 0 else 2^n - x.val,
     begin
       by_cases (x.val = 0),
       { simp [h], apply pos_pow_of_pos, dec_trivial_tac },
       { simp [h],
         have pos : 0 < 2^n - x.val, { apply nat.sub_pos_of_lt x.property },
         have x_val_pos: 0 < x.val, { apply nat.pos_of_ne_zero h },
         apply sub_lt_of_pos_le x.val (2^n) x_val_pos,
         apply le_of_lt x.property,
       }
      end⟩

  -- Add with carry (no overflow)
  @[reducible]
  def adc (x y : bitvec n) (c : bool) : bitvec n × bool :=
    let c₁ := if c then 1 else 0,
        r  := x.val + y.val + c₁ in
    ⟨ ⟨r % 2^n, by simp [in_range] ⟩, r ≥ 2^n ⟩

  @[reducible]
  protected def add (x y : bitvec n) : bitvec n := (adc x y ff).1

  -- Subtract with borrow
  @[reducible]
  def sbb (x y : bitvec n) (b : bool) : bool × bitvec n :=
    let b₁ : bitvec n := if b then 1 else 0,
        r  := match bitvec.adc x (bitvec.neg y) ff with
              | (z, b₂) := bitvec.adc z (bitvec.neg b₁) ff
              end
    in ⟨ if b then y.val + 1 > x.val else y.val > x.val , r.1 ⟩

  @[reducible]
  protected def sub (x y : bitvec n) : bitvec n := (sbb x y ff).2

  instance : has_add (bitvec n)  := ⟨bitvec.add⟩
  instance : has_sub (bitvec n)  := ⟨bitvec.sub⟩
  instance : has_neg (bitvec n)  := ⟨bitvec.neg⟩

  @[reducible]
  protected def mul (x y : bitvec n) : bitvec n :=
    ⟨ (x.val * y.val) % 2^n, by simp [in_range] ⟩

  instance : has_mul (bitvec n)  := ⟨bitvec.mul⟩
end arith

section comparison
  variable {n : ℕ}

  @[reducible]
  def uborrow (x y : bitvec n) : bool := prod.fst (sbb x y ff)

  @[reducible]
  def ult (x y : bitvec n) : Prop := uborrow x y
  @[reducible]
  def ugt (x y : bitvec n) : Prop := ult y x

  @[reducible]
  def ule (x y : bitvec n) : Prop := ¬ (ult y x)
  @[reducible]
  def uge (x y : bitvec n) : Prop := ule y x

  def sborrow : Π {n : ℕ}, bitvec n → bitvec n → bool
  | 0        _ _ := ff
  | (succ n) x y :=
    match (msb x, msb y) with
    | (tt, ff) := tt
    | (ff, tt) := ff
    | (ff, ff) := uborrow x y
    | (tt, tt) := uborrow (bitvec.neg y) (bitvec.neg x) -- -x < -y when y < x
    end

  @[reducible]
  def slt (x y : bitvec n) : Prop := sborrow x y
  @[reducible]
  def sgt (x y : bitvec n) : Prop := slt y x
  @[reducible]
  def sle (x y : bitvec n) : Prop := ¬ (slt y x)
  @[reducible]
  def sge (x y : bitvec n) : Prop := sle y x

end comparison

section conversion
  variable {α : Type}

  @[reducible]
  protected def of_nat (n : ℕ) (x:ℕ) : bitvec n := ⟨ x % 2^n, by simp [in_range] ⟩

  @[reducible]
  protected def of_int : Π (n : ℕ), int → bitvec (succ n)
  | n (int.of_nat m)          := bitvec.of_nat (succ n) m
  | n (int.neg_succ_of_nat m) := bitvec.neg (bitvec.of_nat (succ n) m)

  @[reducible]
  protected def to_nat {n : nat} (v : bitvec n) : nat := v.val

  theorem of_nat_to_nat {n : ℕ} (x : bitvec n)
  : bitvec.of_nat n (bitvec.to_nat x) = x :=
    begin
      cases x,
      simp [bitvec.to_nat, bitvec.of_nat],
      apply mod_eq_of_lt x_property,
    end

  theorem to_nat_of_nat {k n : ℕ}
  : bitvec.to_nat (bitvec.of_nat k n) = n % 2^k :=
    begin
      simp [bitvec.of_nat, bitvec.to_nat]
    end

  protected def to_int {n:ℕ} (x: bitvec n) : int :=
    match msb x with
    | ff := int.of_nat x.val
    | tt := int.neg_of_nat (bitvec.neg x).val
    end

end conversion

instance (n : nat) : has_repr (bitvec n) :=
⟨repr⟩
end bitvec

instance {n} {x y : bitvec n} : decidable (bitvec.ult x y) := bool.decidable_eq _ _
instance {n} {x y : bitvec n} : decidable (bitvec.ugt x y) := bool.decidable_eq _ _
