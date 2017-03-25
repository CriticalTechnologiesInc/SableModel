theory Memory
imports
  "../AutoCorres/Impl"
begin

abbreviation "HEAP_SIZE \<equiv> 1024" (* in blocks *)

locale sable_m = sable_isa +
(*assumes heap: "\<forall>p \<in> set (array_addrs (Ptr (symbol_table ''heap'') :: mem_node_C ptr) HEAP_SIZE). c_guard p"*)
assumes heap: "c_guard (Ptr (symbol_table ''heap'') :: (mem_node_C[1024]) ptr)"
begin

definition
  heap_invs :: "globals \<Rightarrow> bool"
where  
  "heap_invs s \<equiv> (*c_guard (node_' s) \<and>
    ptr_val (node_' s) \<in> {symbol_table ''heap''..+size_of TYPE(mem_node_C) * HEAP_SIZE} \<and>*)
    (let (node_size :: 32 word) = mem_node_C.size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s)) in
    node_' s +\<^sub>p (uint node_size + 1) = Ptr (symbol_table ''heap'') +\<^sub>p HEAP_SIZE)"

lemma intvl_p: "0 \<le> i \<Longrightarrow> 0 < size_of TYPE('a) \<Longrightarrow> size_of TYPE('a) * nat i < n
  \<Longrightarrow> ptr_val ((Ptr p :: ('a :: c_type) ptr) +\<^sub>p i) \<in> {p..+n}"
unfolding intvl_def
apply auto
apply (rule exI [where x="size_of TYPE('a) * nat i"])
unfolding ptr_add_def apply simp
done

(*declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]*)

lemma init_heap'_invs: "\<lbrace>\<lambda>s. node_' s = NULL\<rbrace> init_heap' \<lbrace>\<lambda>_ s. (heap_invs s)\<rbrace>!"
unfolding init_heap'_def heap_invs_def fail'_def FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def
apply wp
apply (auto simp add: ptr_sub_def h_val_id intvl_self heap)
using TypHeapLib.c_guard_array_c_guard heap apply force
done

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

lemma alloc'_invs: "align_of TYPE('a :: c_type) dvd 8 \<Longrightarrow> n > 0
  \<Longrightarrow> \<lbrace>\<lambda>s. heap_invs s\<rbrace> alloc' n
      \<lbrace>\<lambda>r s. heap_invs s(* \<and> (ptr_val r \<noteq> 0 \<longrightarrow> c_guard ((ptr_coerce r) :: 'a ptr))*)\<rbrace>"
unfolding alloc'_def heap_invs_def fail'_def FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def
apply (simp add: h_val_field_from_bytes ptr_add_def)
apply wp
apply (simp add: h_val_id)
done

(*apply (auto simp add: h_val_field_from_bytes shiftr2_is_div_4 h_val_id)
apply (simp add: ptr_add_def ptr_sub_def)
proof -
  fix s :: globals
  let ?node = "ptr_val (node_' s)" and ?heap = "symbol_table ''heap''"
  let ?node_size = "size_C (h_val (hrs_mem (t_hrs_' s)) (node_' s))"
  let ?blocks = "(scast (ucast n div 4 :: 32 signed word) + 1) :: 16 word"
  assume a1: "uint (scast (ucast (?node - ?heap) div 4)) + uint ?node_size = 2047"
     and a2: "\<not> uint ?node_size \<le> uint ?blocks"
  from a2 have "uint ?blocks < uint ?node_size" by auto
  have "uint (?blocks) * 4 + 4 = uint (?blocks + 1) * 4" apply unat_arith
  have "uint ((scast ((ucast (?node + (of_int (uint (?blocks)) * 4 + 4) - ?heap) :: 32 signed word) div 4)) :: 16 word)
    = uint ((scast ((ucast (?node - ?heap) :: 32 signed word) div 4)) :: 16 word) + uint (?blocks) + 1"
    
  have "uint ((scast ((ucast (?node + (of_int (uint (?blocks)) * 4 + 4) - ?heap) :: 32 signed word) div 4)) :: 16 word) +
         uint (?node_size - (?blocks + 1)) = 2047" sorry
  thus "uint ((scast ((ucast (?node + (of_int (uint (?blocks)) * 4 + 4) - ?heap) :: 32 signed word) div 4)) :: 16 word) +
         uint (?node_size - (2 + (scast ((ucast n div 4) :: 32 signed word)) :: 16 word)) = 2047" by simp*)


lemma alloc'_hoare: "n > 0 \<Longrightarrow> \<lbrace>heap_invs\<rbrace> alloc' n
  \<lbrace>\<lambda>r s. (heap_invs s) \<and> (ptr_val r \<noteq> 0 \<longrightarrow> c_guard r)\<rbrace>"
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