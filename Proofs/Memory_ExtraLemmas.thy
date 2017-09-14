theory Memory_ExtraLemmas
  imports
    "../AutoCorres/Impl"
    "../lib/ExtraLemmas"
    "$ISABELLE_HOME/src/HOL/Library/LaTeXsugar"
    
begin
  
lemma contrapos: "(P \<longrightarrow> Q) = (\<not>Q \<longrightarrow> \<not>P)"
  by blast

lemma unat_add_le: "unat (a + b) \<le> unat (a::('a::len word)) + unat b "
  by unat_arith

lemma eight_eq_eight : "unat (8::32 word) = 8" by simp

lemma intvl_no_overflow_lower_bound:
  "(a :: ('a::{len}) word) \<in> {x ..+  sz} \<Longrightarrow> unat x + sz \<le> 2 ^ LENGTH('a) \<Longrightarrow> a \<ge> x"
  apply unat_arith unfolding intvl_def  apply unat_arith
  apply auto 
  apply (subgoal_tac "unat (of_nat k) = k")
   apply (smt add.commute add_leD1 add_less_mono1 order_less_le_trans unat_of_nat unat_of_nat_eq word_nchotomy)
  by (smt add.commute add.left_neutral add_diff_cancel_right' add_leD1 add_lessD1 diff_add_inverse 
      diff_diff_cancel diff_le_self le_Suc_ex less_diff_conv less_irrefl_nat less_or_eq_imp_le 
      linorder_not_less nat_add_left_cancel_less nat_less_le not_add_less1 order_less_le_trans unat_of_nat_eq)
    
lemma intvl_upper_bound: "a \<in> {x ..+ sz} \<Longrightarrow> 
  unat a < unat x + sz"
  unfolding intvl_def
  apply unat_arith
  apply (auto simp add: unat_of_nat) 
  using mod_less by blast
    
lemma zero_not_in_intvl_lower_bound:
  "(a::('a::len) word) \<in> {x ..+ sz} \<Longrightarrow> 0 \<notin> {x ..+  sz}  \<Longrightarrow> a \<ge>  x "
  apply (drule zero_not_in_intvl_no_overflow)
  by (rule intvl_no_overflow_lower_bound)

lemma split_goal:"(P \<longrightarrow> Q) \<Longrightarrow> (\<not>P \<longrightarrow> Q) \<Longrightarrow> Q" 
  by auto

lemma word_div_mult_lower_bound: 
  assumes "unat x + unat y < 2 ^ 32"
    and "y \<noteq> 0"   
  shows "((x:: word32) div ( y :: word32)) * y + y \<ge> x"
proof -
  have "unat ((x div y) * y) = unat (x div y) * unat y"
    apply unat_arith
    apply auto
    by (metis (no_types, hide_lams) Word_Miscellaneous.dtle le_unat_uoi unat_div word_arith_nat_mult)
  have "unat ((x div y) * y) = (unat x div unat y) * unat y"
    apply unat_arith
    apply auto
    by (simp add: \<open>unat (x div y * y) = unat (x div y) * unat y\<close> unat_div)
  have "unat x div unat y * unat y + unat x mod unat y = unat x"
    by simp
  show ?thesis
    using `unat x + unat y < 2 ^ 32` `y \<noteq> 0` 
      `unat ((x div y) * y) = (unat x div unat y) * unat y`
  apply unat_arith
  apply auto  
   apply unat_arith
     apply auto
    apply (subgoal_tac "unat x div unat y * unat y + unat x mod unat y = unat x")
     apply (metis mod_le_divisor nat_add_left_cancel_le)
     apply simp
    using `unat x div unat y * unat y + unat x mod unat y = unat x`
      by arith
qed

lemma scast_NOT_simp: "(scast (~~(flag :: 32 signed word)) :: word32) = ~~ ((scast flag)::word32)"
  unfolding word_not_def
  apply (subst scast_down_wi)
   defer
   apply (subst uint_scast)
   apply (rule refl)
  apply (subst is_down)
  by simp  

    
(* Unused *) 
(*
lemma c_guard_l1:
  assumes "c_guard (a::('a::mem_type) ptr)"
    "\<not> c_guard (a +\<^sub>p 1)"
    "b > a" 
    "b \<ge> a +\<^sub>p 1"
  shows "\<not> c_null_guard b" 
proof -
  have "\<not> c_null_guard ( a +\<^sub>p 1)" using `c_guard a` `\<not> c_guard (a +\<^sub>p 1)`
    unfolding c_guard_def apply auto    
    apply(frule ptr_aligned_plus[where i = 1]) by auto
  hence "0 \<in> ptr_span (a +\<^sub>p 1)" unfolding c_null_guard_def by auto
  have "0 \<in> ptr_span b" using `b \<ge> a +\<^sub>p 1` using `0 \<in> ptr_span (a +\<^sub>p 1)` unfolding intvl_def
  proof simp
    assume "a +\<^sub>p 1 \<le> b"
      and "\<exists>k. ptr_val (a +\<^sub>p 1) + of_nat k = 0 \<and> k < size_of TYPE('a)"
    then obtain k where k:"ptr_val (a +\<^sub>p 1) + of_nat k = 0 \<and> k < size_of TYPE('a)" by auto
    hence "ptr_val (a +\<^sub>p 1) + of_nat k = 0" by auto
    {
      assume "((of_nat k)::32 word) \<noteq> 0"
      have "ptr_val b \<ge> ptr_val (a +\<^sub>p 1)" using `b \<ge> a +\<^sub>p 1`  by (simp add: ptr_le_def ptr_le_def')
      hence 1:"ptr_val b - ptr_val (a +\<^sub>p 1) \<le> of_nat k" 
        using `ptr_val (a +\<^sub>p 1) + of_nat k = 0`
        apply unat_arith apply auto
        using `of_nat k \<noteq> 0` 
        apply (subgoal_tac "unat ((of_nat k)::32 word) = 0 \<Longrightarrow> ((of_nat k)::32 word) = 0")
         apply auto[1]
        apply (subst (asm) (3) unat_eq_0)  by auto
          
      let ?k2' = "of_nat k - ( ptr_val b - ptr_val (a +\<^sub>p 1))"
      have "ptr_val b + ?k2' = of_nat k + ptr_val (a +\<^sub>p 1)" by simp
      hence "ptr_val b + ?k2' = 0" using k by (simp add: add.commute)
      hence 2:"ptr_val b + of_nat (unat ?k2') = 0" by simp
          
      let ?of_nat_k = "((of_nat k):: 32 word)"
      have "?k2' \<le> ?of_nat_k" using 1  word_sub_le by auto
      hence "unat ?k2' \<le> unat ?of_nat_k" by (simp add: word_le_nat_alt) 
      moreover have "unat ?of_nat_k \<le> k" by (metis le_cases le_unat_uoi) 
      moreover  have "k < size_of TYPE('a)" using k by simp
      ultimately have "(unat ?k2') < size_of TYPE('a)" by simp
      hence "ptr_val b + of_nat (unat ?k2') = 0 \<and> (unat ?k2') < size_of TYPE('a)" using 2 by simp
      hence "\<exists>k::nat. ptr_val b + of_nat k = (0::32 word) \<and> k < size_of TYPE('a)" by (frule exI)
    }
    moreover{  
      assume k_eq_0:"((of_nat k)::32 word) = 0" 
      let ?k2' = "of_nat (size_of TYPE('a)) - ( ptr_val b - ptr_val a)"
      have "ptr_val b > ptr_val a" using `b>a` 
        by (simp add: ptr_less_def ptr_less_def')
      hence "unat (ptr_val b) > unat (ptr_val a)" using unat_mono by auto
      from k_eq_0 have "ptr_val (a +\<^sub>p 1)= 0" using k by unat_arith
      hence 1:"ptr_val a + of_nat (size_of TYPE('a)) = 0" unfolding ptr_add_def by simp
      hence 2: "ptr_val b - ptr_val a < of_nat (size_of TYPE('a))" 
        using k_eq_0
        apply unat_arith (* SLOW! *) apply auto
         apply (subgoal_tac "unat (ptr_val a) \<noteq> (0::nat)")
          apply auto[1]
        using `c_guard a` 
         apply (metis len_of_addr_card max_size mem_type_simps(3) neq0_conv unat_of_nat_len)
        using `unat (ptr_val b) > unat (ptr_val a)` by simp
      hence "ptr_val b + ?k2' = 0" using 1  by (simp add: add.commute)
      hence 3:"ptr_val b + of_nat (unat ?k2') = 0" by simp
      have "ptr_val b - ptr_val a > 0" using `ptr_val b > ptr_val a` 
        using word_neq_0_conv by fastforce 
      with 2 have "?k2' < of_nat (size_of TYPE('a))"  by unat_arith (* VERY SLOW! *)
      hence "unat ?k2' < size_of TYPE('a)" using unat_less_helper by auto
      with 3 have "ptr_val b + of_nat (unat ?k2') = 0 \<and> unat ?k2' < size_of TYPE('a)" by auto
      hence "\<exists>k::nat. ptr_val b + of_nat k = (0::32 word) \<and> k < size_of TYPE('a)" by (frule exI)  
    }
    ultimately show "\<exists>k::nat. ptr_val b + of_nat k = (0::32 word) \<and> k < size_of TYPE('a)"
      by auto
  qed 
  thus "\<not> c_null_guard b" unfolding c_null_guard_def by auto
qed
*)
   
lemma unat_add_lem_3:
  "unat (a::'a::len word) + unat b + unat c < 2 ^ LENGTH('a) =
    (unat (a + b + c) = unat a + unat b + unat c)"
  using unat_add_lem
  by (metis add_lessD1 unat_lt2p) 
    
lemma unat_addition_less_pres:"unat (a::'a::len word) + unat b < unat c \<Longrightarrow> a + b < c"
  by unat_arith
    
lemma unat_addition_le_pres:"unat (a::'a::len word) + unat b \<le> unat c \<Longrightarrow> a + b \<le> c"
  by unat_arith
    
lemma shiftr3_upper_bound:"(x :: 32 word) >> 3 \<le> 0x1FFFFFFF"
  apply (simp add:shiftr3_is_div_8)
  apply unat_arith
  by auto
  
lemma intvl_no_overflow2:
  assumes asm: "unat (a::'a::len word) + b \<le> 2 ^ LENGTH('a)"
  shows "(x \<in> {a..+b}) = (a \<le> x \<and> unat x < unat a + b)"
proof -
  {
    assume "x \<in> {a ..+ b}"
    with intvl_no_overflow_lower_bound intvl_upper_bound asm
    have "(a \<le> x \<and> unat x < unat a + b)" by blast    
  }moreover
  {
    assume "(a \<le> x \<and> unat x < unat a + b)"
    thm intvlI   
    have "a + of_nat (unat x - unat a) \<in> {a ..+ b}"
      apply (rule intvlI)
      using `(a \<le> x \<and> unat x < unat a + b)` asm
      by unat_arith
    moreover have "a + of_nat (unat x - unat a) = x" 
      using `(a \<le> x \<and> unat x < unat a + b)` asm
      apply unat_arith
      apply (subgoal_tac "unat (x - a) = unat x - unat a")
       apply auto
      by unat_arith
    ultimately have "x \<in> {a ..+ b}" by argo
  }
  ultimately show ?thesis by fast  
qed

end
