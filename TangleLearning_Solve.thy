theory TangleLearning_Solve
  imports Main ParityGames TangleAttractors TangleLearning_Search
begin

context paritygame begin

type_synonym 'a solve_state = "'a set \<times> 'a set \<times> 'a strat \<times> 'a strat \<times> 'a set \<times> 'a set set"
definition solve_state_W\<^sub>0 :: "'a solve_state \<Rightarrow> 'a set" where
  "solve_state_W\<^sub>0 \<equiv> \<lambda>(W\<^sub>0,W\<^sub>1,\<sigma>\<^sub>0,\<sigma>\<^sub>1,R,T). W\<^sub>0"

definition solve_state_W\<^sub>1 :: "'a solve_state \<Rightarrow> 'a set" where
  "solve_state_W\<^sub>1 \<equiv> \<lambda>(W\<^sub>0,W\<^sub>1,\<sigma>\<^sub>0,\<sigma>\<^sub>1,R,T). W\<^sub>1"

definition solve_state_\<sigma>\<^sub>0 :: "'a solve_state \<Rightarrow> 'a strat" where
  "solve_state_\<sigma>\<^sub>0 \<equiv> \<lambda>(W\<^sub>0,W\<^sub>1,\<sigma>\<^sub>0,\<sigma>\<^sub>1,R,T). \<sigma>\<^sub>0"

definition solve_state_\<sigma>\<^sub>1 :: "'a solve_state \<Rightarrow> 'a strat" where
  "solve_state_\<sigma>\<^sub>1 \<equiv> \<lambda>(W\<^sub>0,W\<^sub>1,\<sigma>\<^sub>0,\<sigma>\<^sub>1,R,T). \<sigma>\<^sub>1"

definition solve_state_R :: "'a solve_state \<Rightarrow> 'a set" where
  "solve_state_R \<equiv> \<lambda>(W\<^sub>0,W\<^sub>1,\<sigma>\<^sub>0,\<sigma>\<^sub>1,R,T). R"

definition solve_state_T :: "'a solve_state \<Rightarrow> 'a set set" where
  "solve_state_T \<equiv> \<lambda>(W\<^sub>0,W\<^sub>1,\<sigma>\<^sub>0,\<sigma>\<^sub>1,R,T). T"

inductive solve_step :: "'v solve_state \<Rightarrow> 'v solve_state \<Rightarrow> bool" where
  step: "\<lbrakk>R\<noteq>{}; R \<subseteq> V; paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R);
          search T R Y;
          T' = T \<union> {U | U \<sigma> \<alpha>. U \<in> Y \<and> tangle_strat \<alpha> U \<sigma> \<and> (E `` (U\<inter>V_opponent \<alpha>)) - U \<noteq> {}};
          T\<^sub>0' = {t. t\<in>T' \<and> tangle EVEN t}; T\<^sub>1' = {t. t \<in> T' \<and> tangle ODD t};
          D = {(U,\<sigma>) | U \<sigma> \<alpha>. U \<in> Y \<and> tangle_strat \<alpha> U \<sigma> \<and> (E `` (U\<inter>V_opponent \<alpha>)) \<subseteq> U};
          D\<^sub>0 = {U | U \<sigma>. (U,\<sigma>) \<in> D \<and> strategy_of_player EVEN \<sigma>};
          D\<^sub>1 = {U | U \<sigma>. (U,\<sigma>) \<in> D \<and> strategy_of_player ODD \<sigma>};
          tangle_attractor EVEN T\<^sub>0' (\<Union>D\<^sub>0) W\<^sub>0'' \<sigma>\<^sub>0'';
          tangle_attractor ODD T\<^sub>1' (\<Union>D\<^sub>1) W\<^sub>1'' \<sigma>\<^sub>1'';
          W\<^sub>0' = (if D\<noteq>{} then W\<^sub>0 \<union> W\<^sub>0'' else W\<^sub>0);
          \<sigma>\<^sub>0' = (if D\<noteq>{} then \<sigma>\<^sub>0 ++ \<sigma>\<^sub>0'' else \<sigma>\<^sub>0);
          W\<^sub>1' = (if D\<noteq>{} then W\<^sub>1 \<union> W\<^sub>1'' else W\<^sub>1);
          \<sigma>\<^sub>1' = (if D\<noteq>{} then \<sigma>\<^sub>1 ++ \<sigma>\<^sub>1'' else \<sigma>\<^sub>1);
          R' = (if D\<noteq>{} then R - (W\<^sub>0'\<union>W\<^sub>1') else R)\<rbrakk>
            \<Longrightarrow> solve_step (W\<^sub>0,W\<^sub>1,\<sigma>\<^sub>0,\<sigma>\<^sub>1,R,T) (W\<^sub>0',W\<^sub>1',\<sigma>\<^sub>0',\<sigma>\<^sub>1',R',T')"

lemma solve_step_R_notempty: "solve_step S S' \<Longrightarrow> solve_state_R S \<noteq> {}"
  unfolding solve_state_R_def
  apply (induction rule: solve_step.induct)
  by fast

definition solve :: "'v set \<Rightarrow> 'v set \<Rightarrow> 'v strat \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "solve W\<^sub>0 W\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<equiv> \<exists>T. solve_step\<^sup>*\<^sup>* ({},{},Map.empty,Map.empty,V,{}) (W\<^sub>0,W\<^sub>1,\<sigma>\<^sub>0,\<sigma>\<^sub>1,{},T)"

lemma solve_terminates_on_empty_R: "\<not>Domainp solve_step (W\<^sub>0,W\<^sub>1,\<sigma>\<^sub>0,\<sigma>\<^sub>1,{},T)"
  using solve_step_R_notempty
  unfolding solve_state_R_def
  by fast

lemma tanglelearning_terminates:
  "\<exists>W\<^sub>0 W\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1. solve W\<^sub>0 W\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1"
  sorry

(** TODO: Redefine winning_region to also take a strategy, so we can say that the two strategies
    are also winning strategies. *)
lemma tanglelearning_partially_correct:
  "solve W\<^sub>0 W\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<Longrightarrow>
    V = W\<^sub>0 \<union> W\<^sub>1 \<and> W\<^sub>0 \<inter> W\<^sub>1 = {} \<and>
    winning_region EVEN W\<^sub>0 \<and>
    winning_region ODD W\<^sub>1"
  sorry

(** Tangle learning is correct: it both terminates and gives two winning regions and corresponding
    strategies. *)
theorem tanglelearning_correct:
  "(\<exists>W\<^sub>0 W\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1. solve W\<^sub>0 W\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1) \<and>
   (\<forall>W\<^sub>0 W\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1. solve W\<^sub>0 W\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<longrightarrow>
      V = W\<^sub>0 \<union> W\<^sub>1 \<and> W\<^sub>0 \<inter> W\<^sub>1 = {} \<and>
      winning_region EVEN W\<^sub>0 \<and>
      winning_region ODD W\<^sub>1)"
  using tanglelearning_terminates tanglelearning_partially_correct by blast

end (** End of context paritygame. *)

end