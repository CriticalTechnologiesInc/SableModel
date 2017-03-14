theory Memory
imports
  "../AutoCorres/Impl"
begin

context sable_isa
begin

definition
  heap_invs :: "globals \<Rightarrow> bool"
where  
  "heap_invs s \<equiv> c_guard (node_' s) \<and>
    ptr_val (node_' s) \<in> {symbol_table ''heap''..+size_of TYPE(mem_node_C) * 2048} \<and>
    (let (node_size :: 16 word) = mem_node_C.size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s))
    in scast (node_' s -\<^sub>p Ptr (symbol_table ''heap'')) + node_size + 1 = 2048)"

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

lemma alloc'_invs: "n > 0 \<Longrightarrow> \<lbrace>\<lambda>s. alloc'_invs s\<rbrace> alloc' n \<lbrace>\<lambda>_ s. (alloc'_invs s)\<rbrace>"
unfolding alloc'_def alloc'_invs_def fail'_def FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def
apply simp
apply wp
apply auto
  apply (rule intvl_p)
  apply auto

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