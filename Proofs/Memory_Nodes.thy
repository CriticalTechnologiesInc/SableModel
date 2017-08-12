theory Memory_Nodes
  imports
    "../AutoCorres/Impl"
    "../lib/ExtraLemmas"
begin
  
context sable_isa
begin
  
abbreviation node_size
  where "node_size s n \<equiv> size_C (h_val (hrs_mem (t_hrs_' s)) n)"
abbreviation node_size_masked
  where "node_size_masked s n \<equiv> (node_size s n) && scast (~~ MEM_NODE_OCCUPIED_FLAG)"
    
abbreviation node_next
  where "node_next s n \<equiv> next_C (h_val (hrs_mem (t_hrs_' s)) n)" 
abbreviation node_is_occupied
  where "node_is_occupied s n \<equiv> (mem_node_C.size_C (h_val (hrs_mem (t_hrs_' s)) n)) && scast  MEM_NODE_OCCUPIED_FLAG"

abbreviation node_val
  where "node_val s n \<equiv> (h_val (hrs_mem (t_hrs_' s)) n)"
    
abbreviation update_node :: " globals \<Rightarrow> mem_node_C ptr \<Rightarrow> mem_node_C \<Rightarrow> globals"
  where "update_node s n new_val \<equiv>
  (t_hrs_'_update (hrs_mem_update (heap_update n new_val)) s)"
value t_hrs_'_update
  
abbreviation hrs_the_same_at
  where "hrs_the_same_at s s' p \<equiv>
  fst (t_hrs_' s) p = fst (t_hrs_' s') p \<and> snd (t_hrs_' s) p = snd (t_hrs_' s') p"

lemma t_hrs_'_t_hrs_'_update_simp:
  "t_hrs_' (t_hrs_'_update m (s::globals)) = m (t_hrs_' s)" by simp
    
lemma updated_node_val: 
  "h_val (hrs_mem (t_hrs_' (update_node s n new_val))) n = new_val"
  by (simp add: h_val_heap_update hrs_mem_update)
    
lemma updated_node_size:
  "node_size (update_node s n (mem_node_C nodeSize next)) n = nodeSize"
  using sable_isa.updated_node_val by auto
    
lemma updated_node_next:
  "node_next (update_node s n (mem_node_C nodeSize next)) n = next"
  using sable_isa.updated_node_val by auto
    
lemma hrs_the_same_nodes_the_same:
  "\<forall>p \<in> ptr_span (node::mem_node_C ptr). hrs_the_same_at s s' p \<Longrightarrow>
    node_val s node = node_val s' node"
  unfolding h_val_def hrs_mem_def
  apply (subgoal_tac " heap_list (fst (t_hrs_' s)) (size_of TYPE(mem_node_C)) (ptr_val node) =
     heap_list (fst (t_hrs_' s')) (size_of TYPE(mem_node_C)) (ptr_val node)")
   apply auto
  apply (rule heap_list_h_eq2)
  by simp

typ "heap_typ_desc" 
typ "heap_mem"
typ "heap_raw_state"

value "t_hrs_'"
value "hrs_mem"
value "hrs_htd"
  
lemma MEM_NODE_OCCUPIED_FLAG_not_zero:
  "MEM_NODE_OCCUPIED_FLAG \<noteq> (0:: 32 signed word)" unfolding MEM_NODE_OCCUPIED_FLAG_def by auto

lemma one_mask_neg_MNOF_not_zero[simp]:
  "(1::32 signed word) && ~~ MEM_NODE_OCCUPIED_FLAG = (0::32 signed word) \<Longrightarrow> False"
     unfolding MEM_NODE_OCCUPIED_FLAG_def by unat_arith

abbreviation
  array_span :: "'a::mem_type ptr \<Rightarrow> nat \<Rightarrow> addr set" where
  "array_span p arr_size \<equiv> {ptr_val p ..+ arr_size * size_of TYPE('a)}"

end  
end
  
  