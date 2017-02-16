theory StateRelation
imports
  TPM_Relation
  "../Abstract/Abstract"
begin

context sable_verified
begin

definition
  TPM_SESSION_rel :: "(TPM.AUTHHANDLE \<times> Session) \<Rightarrow> tdTPM_SESSION_C \<Rightarrow> bool"
where
  "TPM_SESSION_rel x s' \<equiv> case x of (h, s) \<Rightarrow>
    of_nat h = tdTPM_SESSION_C.authHandle_C s' \<and>
    NONCE_rel (Session.nonceEven s) (tdTPM_SESSION_C.nonceEven_C s') \<and>
    NONCE_rel (Session.nonceOdd s) (tdTPM_SESSION_C.nonceOdd_C s') \<and>
    BOOL_rel (Session.continue s) (tdTPM_SESSION_C.continueAuthSession_C s')"

definition
  R :: "(astate \<times> lifted_globals) set"
where
  "R \<equiv> {(s, s'). (powerOn \<circ> machine) s \<and> (powerOn \<circ> phantom_machine_state_'') s' \<longrightarrow>
       (let sess_deref = \<lambda>p'. heap_tdTPM_SESSION_C s' (heap_tdTPM_SESSION_C'ptr s' p') in
       let sess_valid = \<lambda>p'. is_valid_tdTPM_SESSION_C'ptr s' p' \<and> is_valid_tdTPM_SESSION_C s'
              (heap_tdTPM_SESSION_C'ptr s' p') in
         Ball (set (array_addrs (Ptr (symbol_table ''sessions'')) 2))
             (\<lambda>p'. sess_valid p'
             \<longrightarrow> (\<forall>sess. \<exists>h. sessions s h = Some sess \<and> TPM_SESSION_rel (h, sess) (sess_deref p')))
         \<and> (\<forall>sess h. sessions s h = Some sess \<longrightarrow>
              Bex (set (array_addrs (Ptr (symbol_table ''sessions'')) 2))
             (\<lambda>p'. sess_valid p' \<and> TPM_SESSION_rel (h, sess) (sess_deref p'))))}"

end

end