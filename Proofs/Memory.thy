theory Memory
imports
  "../AutoCorres/Impl"
begin

context sable_isa
begin

abbreviation "HEAP_SIZE \<equiv> 2048" (* in blocks *)

definition
  heap_invs :: "globals \<Rightarrow> bool"
where  
  "heap_invs s \<equiv> c_guard (node_' s) \<and>
    (*ptr_val (node_' s) \<in> {symbol_table ''heap''..+size_of TYPE(mem_node_C) * HEAP_SIZE} \<and>*)
    (let (node_size :: 16 word) = mem_node_C.size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s)) in
    (let (node_offset :: 16 word) = scast (node_' s -\<^sub>p Ptr (symbol_table ''heap'')) in
    uint node_offset + uint node_size + 1 = HEAP_SIZE))"

lemma intvl_p: "0 \<le> i \<Longrightarrow> 0 < size_of TYPE('a) \<Longrightarrow> size_of TYPE('a) * nat i < n
  \<Longrightarrow> ptr_val ((Ptr p :: ('a :: c_type) ptr) +\<^sub>p i) \<in> {p..+n}"
unfolding intvl_def
apply auto
apply (rule exI [where x="size_of TYPE('a) * nat i"])
unfolding ptr_add_def apply simp
done

lemma init_heap'_invs: "\<lbrace>\<lambda>s. node_' s = NULL\<rbrace> init_heap' \<lbrace>\<lambda>_ s. (heap_invs s)\<rbrace>"
unfolding init_heap'_def heap_invs_def fail'_def FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def
apply wp
apply (auto simp add: ptr_sub_def h_val_id intvl_self)
done

(*declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]*)

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

lemma alloc'_invs: "n > 0 \<Longrightarrow> \<lbrace>\<lambda>s. heap_invs s\<rbrace> alloc' n \<lbrace>\<lambda>_ s. heap_invs s\<rbrace>"
unfolding alloc'_def heap_invs_def fail'_def FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def
apply simp
apply wp
apply (auto simp add: h_val_field_from_bytes shiftr2_is_div_4 h_val_id)
apply (simp add: ptr_add_def ptr_sub_def)

  apply (rule intvl_p)
  apply (simp add: ptr_sub_def shiftr2_is_div_4)+
proof -
  fix s :: globals
  let ?node_offset = "(ucast (ptr_val (node_' s) - symbol_table ''heap'') div 4) :: 32 signed word"
  let ?node_size = "size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s))"
  let ?blocks = "(scast (ucast n div 4 :: 32 signed word) + 1) :: 16 word"
  assume a1: "uint (scast ?node_offset :: 16 word) + uint ?node_size = 2047"
     and a2: "\<not> uint ?node_size \<le> uint ?blocks"
  from a2 have "uint ?blocks < uint ?node_size" by auto
  with a1 have "uint (scast ?node_offset :: 16 word) + uint ?blocks < 2047" by auto
  moreover have "uint ((scast ?node_offset :: 16 word) + ?blocks) \<le>
    uint (scast ?node_offset :: 16 word) + uint ?blocks" by (simp add: uint_add_le)
  ultimately have "uint ((scast ?node_offset :: 16 word) + ?blocks) < 2047" by auto
  hence "nat (uint ((scast ?node_offset :: 16 word) + ?blocks)) < 2047" by auto
  thus "nat (uint (2 + (scast ?node_offset + scast (ucast n div 4)))) < 2048"
    apply unat_arith


lemma alloc'_hoare: "n > 0 \<Longrightarrow> \<lbrace>alloc'_invs\<rbrace> alloc' n
  \<lbrace>\<lambda>r s. (alloc'_invs s) \<and> (ptr_val r \<noteq> 0 \<longrightarrow> c_guard r)\<rbrace>"
unfolding alloc'_def
apply simp
apply (rule hoare_seq_ext [where B="\<lambda>_ s. alloc'_invs s"])
prefer 2
apply wp_once_trace
apply (rule hoare_seq_ext [where B="\<lambda>_ s. alloc'_invs s"])
apply wp_once_trace
apply auto
apply (rule hoare_seq_ext)
apply wp_once_trace

end

end