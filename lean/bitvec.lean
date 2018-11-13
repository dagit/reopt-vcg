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

-- local infix `++ₜ`:65 := vector.append

-- Create a zero bitvector
@[reducible] protected
def zero (n : ℕ) : bitvec n :=
  ⟨0, nat.pos_pow_of_pos n dec_trivial⟩

instance {n:ℕ} : has_zero (bitvec n) := ⟨bitvec.zero n⟩

-- Create a bitvector with the constant one.
@[reducible] protected
def one (n: ℕ) {H : n > 0} : bitvec n :=
  ⟨1, calc
        1   < 2   : by dec_trivial_tac
        ... = 2^1 : by trivial
        ... ≤ 2^n : by apply (pow_le_pow_of_le_right (zero_lt_succ _) (succ_le_of_lt H))⟩

instance {n:ℕ} {H: n > 0} : has_one (bitvec n)  := ⟨@bitvec.one n H⟩

protected def cong {a b : ℕ} (h : a = b) : bitvec a → bitvec b
| ⟨x, p⟩ := ⟨x, h ▸ p⟩

lemma in_range (x n : ℕ) : x % 2 ^ n < 2 ^ n :=
  begin
    apply (mod_lt _),
    apply (pos_pow_of_pos _ _),
    simp [zero_lt_succ]
  end

lemma div_lt_of_lt_mul {m n : ℕ} : ∀ {k} {Hk : k > 0}, m < k * n → m / k < n
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

lemma sub_add_big_med_small (a b c : ℕ) (Hab: a > b) (Hbc : b > c) : a - b + c < a :=
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
  def msb (x: bitvec n) : bool := (shl x (n-1)).val = 1

  @[reducible]
  def lsb (x: bitvec n) : bool := x.val % 2 = 1

  -- unsigned shift right
  @[reducible]
  def ushr (x : bitvec n) (i : ℕ) : bitvec n := ⟨x.val / 2^i,
    calc
        x.val / 2^i ≤ x.val : by apply nat.div_le_self
                ... < 2^n   : by exact x.property⟩

  -- signed shift right
  @[reducible]
  def sshr (x: bitvec n) (i:ℕ) {Hi_lt_n: i ≤ n} : bitvec n :=
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
          cases i,
          { simp, rw nat.sub_self (2^n), simp, exact x.property },
          { have : x.val/2^succ i < 2^(n-succ i),
            { apply div_lt_of_lt_mul,
              apply pos_pow_of_pos,
              dec_trivial_tac,
              rw [pow_mul, add_sub_of_le],
              apply x.property,
              exact Hi_lt_n
            },
            apply sub_add_big_med_small (2^n) (2^(n-succ i)) (x.val/2^(succ i)) _ this,
            have : 2^n > 2^(n-succ i),
            { apply pow_lt_pow_of_lt_right (lt_succ_self _)
                                           (sub_lt_of_pos_le _ _ (nat.zero_lt_succ i) Hi_lt_n)
            },
            assumption
          },
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

  def and {w:ℕ} : bitvec w → bitvec w → bitvec w := bitwise band
  def or  {w:ℕ} : bitvec w → bitvec w → bitvec w := bitwise bor
  def xor {w:ℕ} : bitvec w → bitvec w → bitvec w := bitwise bxor

end bitwise

section arith
  variable {n : ℕ}

  protected def xor3 (x y c : bool) := bxor (bxor x y) c
  protected def carry (x y c : bool) :=
  x && y || x && c || y && c

  protected def neg (x : bitvec n) : bitvec n :=
  let f := λ y c, (y || c, bxor y c) in
  prod.snd (map_accumr f x ff)

  -- Add with carry (no overflow)
  def adc (x y : bitvec n) (c : bool) : bitvec (n+1) :=
  let f := λ x y c, (bitvec.carry x y c, bitvec.xor3 x y c) in
  let ⟨c, z⟩ := vector.map_accumr₂ f x y c in
  c :: z

  protected def add (x y : bitvec n) : bitvec n := tail (adc x y ff)

  -- Subtract with borrow
  def sbb (x y : bitvec n) (b : bool) : bool × bitvec n :=
  let f := λ x y c, (bitvec.carry (bnot x) y c, bitvec.xor3 x y c) in
  vector.map_accumr₂ f x y b

  protected def sub (x y : bitvec n) : bitvec n := prod.snd (sbb x y ff)

  instance : has_zero (bitvec n) := ⟨bitvec.zero n⟩

  instance : has_add (bitvec n)  := ⟨bitvec.add⟩
  instance : has_sub (bitvec n)  := ⟨bitvec.sub⟩
  instance : has_neg (bitvec n)  := ⟨bitvec.neg⟩

  protected def mul (x y : bitvec n) : bitvec n :=
  let f := λ r b, cond b (r + r + y) (r + r) in
  (to_list x).foldl f 0

  instance : has_mul (bitvec n)  := ⟨bitvec.mul⟩
end arith

-- bitvec specific version of vector.append
def append {m n} (x: bitvec m) (y: bitvec n) : bitvec (m + n) := shl x n + y

section comparison
  variable {n : ℕ}

  def uborrow (x y : bitvec n) : bool := prod.fst (sbb x y ff)

  def ult (x y : bitvec n) : Prop := uborrow x y
  def ugt (x y : bitvec n) : Prop := ult y x

  def ule (x y : bitvec n) : Prop := ¬ (ult y x)
  def uge (x y : bitvec n) : Prop := ule y x

  def sborrow : Π {n : ℕ}, bitvec n → bitvec n → bool
  | 0        _ _ := ff
  | (succ n) x y :=
    match (head x, head y) with
    | (tt, ff) := tt
    | (ff, tt) := ff
    | _        := uborrow (tail x) (tail y)
    end

  def slt (x y : bitvec n) : Prop := sborrow x y
  def sgt (x y : bitvec n) : Prop := slt y x
  def sle (x y : bitvec n) : Prop := ¬ (slt y x)
  def sge (x y : bitvec n) : Prop := sle y x

end comparison

section conversion
  variable {α : Type}

  protected def of_nat : Π (n : ℕ), nat → bitvec n
  | 0        x := nil
  | (succ n) x := of_nat n (x / 2) ++ₜ to_bool (x % 2 = 1) :: nil

  protected def of_int : Π (n : ℕ), int → bitvec (succ n)
  | n (int.of_nat m)          := ff :: bitvec.of_nat n m
  | n (int.neg_succ_of_nat m) := tt :: not (bitvec.of_nat n m)

  def add_lsb (r : ℕ) (b : bool) := r + r + cond b 1 0

  def bits_to_nat (v : list bool) : nat :=
  v.foldl add_lsb 0

  protected def to_nat {n : nat} (v : bitvec n) : nat :=
  bits_to_nat (to_list v)

  theorem bits_to_nat_to_list {n : ℕ} (x : bitvec n)
  : bitvec.to_nat x = bits_to_nat (vector.to_list x)  := rfl

  local attribute [simp] add_comm add_assoc add_left_comm mul_comm mul_assoc mul_left_comm

  theorem to_nat_append {m : ℕ} (xs : bitvec m) (b : bool)
  : bitvec.to_nat (xs ++ₜ b::nil) = bitvec.to_nat xs * 2 + bitvec.to_nat (b::nil) :=
  begin
    cases xs with xs P,
    simp [bits_to_nat_to_list], clear P,
    unfold bits_to_nat list.foldl,
    -- generalize the accumulator of foldl
    generalize h : 0 = x, conv in (add_lsb x b) { rw ←h }, clear h,
    simp,
    induction xs with x xs generalizing x,
    { simp, unfold list.foldl add_lsb, simp [nat.mul_succ] },
    { simp, apply xs_ih }
  end

  theorem bits_to_nat_to_bool (n : ℕ)
  : bitvec.to_nat (to_bool (n % 2 = 1) :: nil) = n % 2 :=
  begin
    simp [bits_to_nat_to_list],
    unfold bits_to_nat add_lsb list.foldl cond,
    simp [cond_to_bool_mod_two],
  end

  theorem of_nat_succ {k n : ℕ}
  :  bitvec.of_nat (succ k) n = bitvec.of_nat k (n / 2) ++ₜ to_bool (n % 2 = 1) :: nil :=
  rfl

  theorem to_nat_of_nat {k n : ℕ}
  : bitvec.to_nat (bitvec.of_nat k n) = n % 2^k :=
  begin
    induction k with k generalizing n,
    { unfold pow nat.pow, simp [nat.mod_one], refl },
    { have h : 0 < 2, { apply le_succ },
      rw [ of_nat_succ
         , to_nat_append
         , k_ih
         , bits_to_nat_to_bool
         , mod_pow_succ h],
      ac_refl, }
  end

  protected def to_int : Π {n : nat}, bitvec n → int
  | 0        _ := 0
  | (succ n) v :=
    cond (head v)
      (int.neg_succ_of_nat $ bitvec.to_nat $ not $ tail v)
      (int.of_nat $ bitvec.to_nat $ tail v)

end conversion

private def repr {n : nat} : bitvec n → string
| ⟨bs, p⟩ :=
  "0b" ++ (bs.map (λ b : bool, if b then '1' else '0')).as_string

instance (n : nat) : has_repr (bitvec n) :=
⟨repr⟩
end bitvec

instance {n} {x y : bitvec n} : decidable (bitvec.ult x y) := bool.decidable_eq _ _
instance {n} {x y : bitvec n} : decidable (bitvec.ugt x y) := bool.decidable_eq _ _
