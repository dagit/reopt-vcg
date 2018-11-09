/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich

Basic operations on bitvectors.

This is a work-in-progress, and contains additions to other theories.
-/
import data.vector

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

-- TODO: is this in the standard library somewhere?
def one_to_the_n (n:ℕ) : (1 ^ n) = 1 :=
  begin
    induction n,
    rw nat.pow_zero,
    rw nat.pow_succ,
    rw n_ih,
    refl
  end

-- Create a bitvector with the constant one.
@[reducible] protected
def one (n: ℕ) {H : n > 0} : bitvec n :=
  ⟨1,
    begin
      intros,

      have one_to_the_n_twice : (1 ^ n) + (1 ^ n) = 2,
        rw one_to_the_n,

      rw [←one_to_the_n n, bit0, one_to_the_n_twice],
      apply (@nat.pow_lt_pow_of_lt_left 1 2 dec_trivial n H),

    end⟩

instance {n:ℕ} {H: n > 0} : has_one (bitvec n)  := ⟨@bitvec.one n H⟩

protected def cong {a b : ℕ} (h : a = b) : bitvec a → bitvec b
| ⟨x, p⟩ := ⟨x, h ▸ p⟩

lemma in_range (x n : ℕ) : x % 2 ^ n < 2 ^ n :=
  begin
    apply (mod_lt _),
    apply (pos_pow_of_pos _ _),
    simp [zero_lt_succ]
  end

lemma div_2_lt {x n:ℕ} (H: x < 2^(n+1)) : x / 2 < 2^n :=
  begin
    rw [pow_succ, ←div_lt_iff_lt_mul] at H,
    exact H,
    apply succ_pos
  end

section shift
  variable {n : ℕ}

  def shl (x : bitvec n) (i : ℕ) : bitvec n := ⟨x.val * 2^i % 2^n, by simp [in_range]⟩

  def msb (x: bitvec n) : bool := (shl x (n-1)).val = 1
  def lsb (x: bitvec n) : bool := x.val % 2 = 1

  -- unsigned shift right
  def ushr (x : bitvec n) (i : ℕ) : bitvec n := ⟨x.val / 2^i,
    calc
        x.val / 2^i ≤ x.val : by apply nat.div_le_self
                ... < 2^n   : by exact x.property⟩

  -- signed shift right
  def sshr {H: n > 0} (x: bitvec n) (i:ℕ) : bitvec n :=
    -- When the sign bit is set in x, (msb x = 1), then we would like
    -- the result of sshr x i, to have the top i bits set.
    -- We can calculate a number that will do this in steps:
    -- 1) (2 ^ n) - 1, will have all the bits set.
    -- 2) (2 ^ (n-i)) - 1, will be a number with the lower (n-i) bits set.
    -- 3) subtract the previous two numbers (1) - (2), to get a
    -- number where only the top i bits are set.
    let upper_bits := 2 ^ n - 1 - (2 ^ (n-i) - 1) in
    ⟨ ((ushr x i).val + if (msb x) then upper_bits else 0) % 2 ^ n,
      by cases (msb x); { simp [upper_bits], apply in_range } ⟩

end shift

def sub_less {a x y : ℕ} (H: x < y) : x - a < y :=
  calc
    x - a ≤ x : sub_le x a
      ... < y : H

lemma mul_lt_self {m k:ℕ} (Hk: k > 0) (Hm: m > 1): k < k * m :=
  begin
    have h: 1 < m,
    { exact Hm },
    have ans: k * 1 < k * m,
    { apply (nat.mul_lt_mul_of_pos_left h Hk) },
    rw mul_one at ans,
    exact ans
  end

@[reducible]
def bit_to_nat : bool → ℕ
  | tt := 1
  | ff := 0

lemma bounded_bit_to_nat {b:bool} : bit_to_nat b ≤ 1 := by cases b; { unfold bit_to_nat, try {apply zero_le} }

lemma sub_right {n m k: ℕ} (H: n + k = m) : n = m - k := by rw [←H, nat.add_sub_cancel]

lemma pow_2_sum {n:ℕ} : 2^(n+1) = 2^n + 2^n :=
  calc
    2^(n+1) = 2^n * 2           : by rw pow_succ
        ... = 2^n * (1 + 1)     : by refl
        ... = 2^n * 1 + 2^n * 1 : by rw nat.left_distrib
        ... = 2^n + 2^n         : by simp

lemma product_eq {n: ℕ} (y:ℕ) (xs : list bool) (len: list.length xs = n) : list.foldl (λacc _, acc*2 + 1) y xs = 2^n * y + 2^n - 1 :=
  begin
    induction xs generalizing n y,
    { simp, simp at len, rw ←len, simp },
    { have len_tl := sub_right len,
      have ih_val := @xs_ih (n-1) (1 + y * 2) len_tl,
      simp, simp at ih_val,
      rw left_distrib (2^(n-1)) at ih_val,
      simp at ih_val, rw ←nat.add_assoc (2^(n-1)) at ih_val,
      have n_pos:  n > 0, { rw [list.length_cons] at len, rw ←len, apply zero_lt_succ},
      have cancel: n - 1 + 1 = n, { apply (succ_pred_eq_of_pos n_pos) },
      have cancel2: succ (n - 1) = n, { apply (succ_pred_eq_of_pos n_pos) },
      rw [eq.symm pow_2_sum, cancel, nat.mul_comm _ 2, ←nat.mul_assoc (2^(n-1)) 2 y, ←pow_succ, cancel2] at ih_val,
      rw nat.mul_comm _ 2, exact ih_val
    }
  end

lemma foldr_append {α β: Type} (f: α → β → β) (y: β) (xs ys: list α) : list.foldr f y (xs ++ ys) = list.foldr f (list.foldr f y ys) xs :=
  begin
    induction xs with xs,
    { refl },
    { simp, rw xs_ih }
  end

lemma reverse_core_cons {α: Type} (ys xs: list α) : list.reverse_core xs ys = list.reverse_core xs list.nil ++ ys :=
  begin
    induction xs with xs generalizing ys,
    { refl },
    { simp [list.reverse_core], rw xs_ih [xs], simp, rw ←xs_ih}
  end

lemma reverse_cons {α: Type} (x: α) (xs: list α) : list.reverse (x :: xs) = list.reverse xs ++ [x] :=
  begin
    induction xs with xs,
    { refl },
    { unfold list.reverse, rw list.reverse_core, rw reverse_core_cons }
  end

lemma foldl_foldr {α β: Type} (f: α → β → α) (y: α) (xs: list β) : list.foldl f y xs = list.foldr (λa b, f b a) y (xs.reverse) :=
  begin
    induction xs with xs generalizing y,
    case list.nil
    { refl },
    case list.cons
    { simp, rw [reverse_cons, foldr_append, xs_ih], refl },
  end

lemma lt_q_r {b q r :ℕ} (Hb: b ≤ 1) (H: q ≤ r) : b + q*2 ≤ 1 + r * 2 :=
  calc
    b + q*2 ≤ 1 + q * 2 : by apply nat.add_le_add_right Hb
        ... ≤ 1 + r * 2 : by apply nat.add_le_add_left (nat.mul_le_mul_right 2 H)

lemma foldr_product_bound {y: ℕ} {xs : list bool} :
    list.foldr (λ (a : bool) (b : ℕ), b * 2 + bit_to_nat a) y xs ≤ list.foldr (λ (a : bool) (b : ℕ), b * 2 + 1) y xs :=
  begin
    induction xs with b,
    case list.nil
    { refl },
    case list.cons
    { simp, apply lt_q_r, apply bounded_bit_to_nat,
      simp at xs_ih,
      apply xs_ih,
    }
  end

lemma product_bound (y: ℕ) (xs : list bool) :
                    list.foldl (λacc b, acc*2 + bit_to_nat b) y xs ≤ list.foldl (λacc _, acc*2 + 1) y xs :=
  begin
    rw [foldl_foldr, foldl_foldr],
    apply foldr_product_bound
  end

section bitwise
  variable {n : ℕ}

  def bitvec_to_bits : Π{n:ℕ} (x: bitvec n), vector bool n
    | 0     _ := nil
    | (n+1) x := msb x :: @bitvec_to_bits n ⟨x.val / 2, by apply (div_2_lt x.property)⟩

  def bits_to_bitvec (x: vector bool n) : bitvec n :=
    ⟨ list.foldl (λacc b, acc*2 + bit_to_nat b) 0 (to_list x),
      begin
        have bounded := product_bound 0 (to_list x),
        rw [product_eq 0 (to_list x) x.property, nat.mul_comm (2^n) 0, zero_mul, zero_add] at bounded,
        have bounded := lt_succ_of_le bounded,
        have pos : 2^n > 0, { apply pos_pow_of_pos, apply succ_pos },
        have succ_rw : succ (2 ^ n - 1) = succ (pred (2 ^ n)), { refl },
        rw [succ_rw, succ_pred_eq_of_pos pos] at bounded,
        exact bounded
      end⟩

  @[reducible]
  def bit_map₂ (f: bool → bool → bool) (x: bitvec n) (y: bitvec n) : bitvec n :=
    bits_to_bitvec (map₂ f (bitvec_to_bits x) (bitvec_to_bits y))

  def not (x: bitvec n) : bitvec n := ⟨2^n - x.val - 1,
    begin
      have xval_pos : 0 < x.val + 1,
      { apply (succ_pos x.val) },
      apply (sub_lt _ xval_pos),
      apply pos_pow_of_pos,
      apply (succ_pos 1)
    end⟩

  def and : bitvec n → bitvec n → bitvec n := bit_map₂ band
  def or  : bitvec n → bitvec n → bitvec n := bit_map₂ bor
  def xor : bitvec n → bitvec n → bitvec n := bit_map₂ bxor

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
