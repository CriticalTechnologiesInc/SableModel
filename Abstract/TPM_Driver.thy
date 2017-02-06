theory TPM_Driver
imports
  AMonad
begin

definition
  TPM_PCRRead :: "PCRINDEX \<Rightarrow> (ERROR + DIGEST) s_monad"
where
  "TPM_PCRRead pcr \<equiv>
   doE
    command \<leftarrow> returnOk \<lparr> TPM.PCRRead_in.pcrIndex = pcr \<rparr>;
    response \<leftarrow> liftE $ tpm_lift (TPM.PCRRead command);
    case (TPM.PCRRead_out.returnCode response) of
      Inl error \<Rightarrow> throwError error
    | Inr () \<Rightarrow> returnOk (TPM.PCRRead_out.outDigest response)
   odE"

definition
  TPM_NV_ReadValue :: "TPM.NV_INDEX \<Rightarrow> nat \<Rightarrow> (TPM.AUTHHANDLE \<times> TPM.AUTHDATA) option
    \<Rightarrow> (TPM.ERROR + ('a :: Hashable)) s_monad"
where
  "TPM_NV_ReadValue idx off a \<equiv>
   doE
    auth \<leftarrow> case a of
              None \<Rightarrow> returnOk (None :: Auth_in option)
            | Some a \<Rightarrow> liftE (
                do
                  session \<leftarrow> gets_the (\<lambda>s. (astate.sessions s) (fst a));
                  inParamDigest \<leftarrow> return [NV_INDEX_dig idx,                          (* 2S *)
                                           nat_dig off];                              (* 3S *)
                  inAuthSetupParams' \<leftarrow> return [DIGEST_dig inParamDigest,             (* 1H1*)
                                                NONCE_dig (Session.nonceEven session),(* 2H1 *)
                                                NONCE_dig (Session.nonceOdd session), (* 3H1 *)
                                                bool_dig (Session.continue session)]; (* 4H1 *)
                  inAuthSetupParams \<leftarrow> return (hmac (snd a) inAuthSetupParams');
                  return (Some \<lparr>
                    Auth_in.authHandle = (fst a),
                    Auth_in.nonceOdd = Session.nonceOdd session,
                    Auth_in.continueAuthSession = Session.continue session,
                    Auth_in.auth = inAuthSetupParams
                  \<rparr>)
                od);
    command \<leftarrow> returnOk \<lparr>
      TPM.NV_ReadValue_in.nvIndex = idx,
      TPM.NV_ReadValue_in.offset = off,
      TPM.NV_ReadValue_in.ownerAuth = auth
    \<rparr>;
    response \<leftarrow> liftE $ tpm_lift (TPM.NV_ReadValue command);
    ret \<leftarrow> case (TPM.NV_ReadValue_out.returnCode response) of
             Inl error \<Rightarrow> throwError error
           | Inr () \<Rightarrow> returnOk (TPM.NV_ReadValue_out.data response);
    case a of
      None \<Rightarrow> returnOk ()
    | Some a \<Rightarrow> liftE (
    do
      session \<leftarrow> gets_the (\<lambda>s. (astate.sessions s) (fst a));
      auth_out \<leftarrow> return (TPM.NV_ReadValue_out.ownerAuth response);
      outParamDigest \<leftarrow> return (hash ret);                                                 (* 4S *)
      outAuthSetupParams' \<leftarrow> return [DIGEST_dig outParamDigest,                            (* 1H1*)
                                     NONCE_dig (TPM.Auth_out.nonceEven auth_out),          (* 2H1 *)
                                     NONCE_dig (Session.nonceOdd session),                 (* 3H1 *)
                                     bool_dig (TPM.Auth_out.continueAuthSession auth_out)];(* 4H1 *)
      outAuthSetupParams \<leftarrow> return (hmac (snd a) outAuthSetupParams');
      when (outAuthSetupParams \<noteq> TPM.Auth_out.auth auth_out)
        reboot;
      return ()
    od);
    returnOk ret
   odE"

thm TPM_NV_ReadValue_def

end