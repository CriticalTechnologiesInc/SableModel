theory ExtraLemmas
imports AutoCorres
begin

lemma shiftr1_is_div_2': "shiftr1 (x :: ('a :: len) word) = x div 2"
apply (simp only: shiftr1_unfold)
using shiftr1_is_div_2 by auto

lemma shiftr2_is_div_4:
assumes "2 < len_of TYPE('a)"
shows "(x :: ('a :: len) word) >> 2 = x div 4"
proof -
  from assms have "x >> 2 = x div 2 ^ 2" by (simp add: shiftr_div_2n_w word_size)
  thus ?thesis by auto
qed

lemma shiftr3_is_div_8:
assumes "3 < len_of TYPE('a)"
shows "(x :: ('a :: len) word) >> 3 = x div 8"
proof -
  from assms have "x >> 3 = x div 2 ^ 3" by (simp add: shiftr_div_2n_w word_size)
  thus ?thesis by auto
qed

lemma array_addrs_ptr_add[intro]: "0 \<le> i \<Longrightarrow> i < int n \<Longrightarrow> p +\<^sub>p i \<in> set (array_addrs p n)"
apply (simp add: set_array_addrs)
apply (rule_tac x="nat i" in exI)
apply simp
done

lemma array_addrs_ptr_ex[dest]:
  "q \<in> set (array_addrs p n)\<Longrightarrow> \<exists>i. q = p +\<^sub>p (int i) \<and> i < n"
by (simp add: set_array_addrs)

lemma ptr_val_inject: "(p :: 'a ptr) = q \<Longrightarrow> ptr_val p = ptr_val q"
by auto

lemma ptr_arith_index: "0 \<le> i \<Longrightarrow> 0 \<le> k
  \<Longrightarrow> nat i * size_of TYPE('a :: wf_type) < 2 ^ len_of TYPE(32)
  \<Longrightarrow> nat k * size_of TYPE('a :: wf_type) < 2 ^ len_of TYPE(32)
  \<Longrightarrow> ((p :: 'a ptr) +\<^sub>p i = p +\<^sub>p k) = (i = k)"
unfolding ptr_add_def
proof auto
  fix i k :: int
  assume size_i: "nat i * size_of TYPE('a) < 4294967296" and "0 \<le> i"
     and size_k: "nat k * size_of TYPE('a) < 4294967296" and "0 \<le> k"
     and eq: "of_int i * of_nat (size_of TYPE('a)) = (of_int k * of_nat (size_of TYPE('a)) :: 32 word)"
  hence "(of_nat (nat i) :: 32 word) * of_nat (size_of TYPE('a))
    = of_nat (nat k) * of_nat (size_of TYPE('a))" by simp
  hence "(of_nat (nat i * size_of TYPE('a)) :: 32 word) = of_nat (nat k * size_of TYPE('a))"
    (is "of_nat ?L = of_nat ?R") by simp
  moreover have "((of_nat ?L :: 32 word) = of_nat ?R) = (?L = ?R)"
    using size_i and size_k by (fastforce intro!: WordLemmaBucket.of_nat_inj)
  ultimately have "?L = ?R" by auto
  thus "i = k" using not_gr0 sz_nzero
    by (metis \<open>0 \<le> i\<close> \<open>0 \<le> k\<close> int_nat_eq mult.commute mult_cancel1)
qed

lemma hoare_post_imp: "\<forall>r s. Q r s \<longrightarrow> R r s \<Longrightarrow> \<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> m \<lbrace>R\<rbrace>"
unfolding valid_def by blast

lemma size_of_le_n[dest]: "size_of TYPE('a :: wf_type) \<le> unat (n :: ('b :: len) word) \<Longrightarrow> 0 < n"
proof -
  fix n :: "'b word"
  assume "size_of TYPE('a) \<le> unat n"
  moreover have "0 < size_of TYPE('a)" using sz_nzero by auto
  ultimately have "0 < unat n" by linarith 
  thus "0 < n" using word_of_nat_less by force
qed

lemma ptr_less_simp : "a < b = (ptr_val a < ptr_val b)" 
  by (simp add: ptr_less_def ptr_less_def')
lemma ptr_le_simp : "a \<le> b = (ptr_val a \<le> ptr_val b)" 
  by (simp add: ptr_le_def ptr_le_def')
lemmas ptr_comp_simps = ptr_less_simp and ptr_le_simp 
end