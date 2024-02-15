theory TangleLearning_Solve
  imports Main ParityGames TangleAttractors TangleLearning_Search
begin

type_synonym 'a solve_state =
  "'a set \<times> 'a set \<times> 'a strat \<times> 'a strat \<times> 'a set \<times> 'a set set"

context paritygame begin

abbreviation (input) filter_T :: "'v set set \<Rightarrow>  player \<Rightarrow> 'v set set" where
  "filter_T T \<alpha> \<equiv> {t. t\<in>T \<and> tangle EVEN t}"

abbreviation (input) filter_D :: "('v set \<times> 'v strat) set \<Rightarrow> player \<Rightarrow> 'v set set" where
  "filter_D D \<alpha> \<equiv> {U | U \<sigma>. (U,\<sigma>)\<in>D \<and> strategy_of_player \<alpha> \<sigma>}"

inductive solve_step :: "'v solve_state \<Rightarrow> 'v solve_state \<Rightarrow> bool" where
  step:
  "\<lbrakk>R\<noteq>{};
    search T R Y;
    T' = T \<union> {U | U \<sigma> \<alpha>. U \<in> Y \<and> tangle_strat \<alpha> U \<sigma> \<and> (E `` (U\<inter>V_opponent \<alpha>)) - U \<noteq> {}};
    D = {(U,\<sigma>) | U \<sigma> \<alpha>. U \<in> Y \<and> tangle_strat \<alpha> U \<sigma> \<and> (E `` (U\<inter>V_opponent \<alpha>)) \<subseteq> U};
    tangle_attractor EVEN (filter_T T EVEN) (\<Union>(filter_D D EVEN)) W\<^sub>0'' \<sigma>\<^sub>0'';
    tangle_attractor ODD (filter_T T ODD) (\<Union>(filter_D D ODD)) W\<^sub>1'' \<sigma>\<^sub>1'';
    W\<^sub>0' = (if D\<noteq>{} then W\<^sub>0 \<union> W\<^sub>0'' else W\<^sub>0);
    \<sigma>\<^sub>0' = (if D\<noteq>{} then \<sigma>\<^sub>0 ++ \<sigma>\<^sub>0'' else \<sigma>\<^sub>0);
    W\<^sub>1' = (if D\<noteq>{} then W\<^sub>1 \<union> W\<^sub>1'' else W\<^sub>1);
    \<sigma>\<^sub>1' = (if D\<noteq>{} then \<sigma>\<^sub>1 ++ \<sigma>\<^sub>1'' else \<sigma>\<^sub>1);
    R' = (if D\<noteq>{} then R - (W\<^sub>0'\<union>W\<^sub>1') else R)\<rbrakk>
      \<Longrightarrow> solve_step (W\<^sub>0,W\<^sub>1,\<sigma>\<^sub>0,\<sigma>\<^sub>1,R,T) (W\<^sub>0',W\<^sub>1',\<sigma>\<^sub>0',\<sigma>\<^sub>1',R',T')"

lemmas solve_step_induct[consumes 1, case_names step] =
  solve_step.induct[
  of "(W\<^sub>0,W\<^sub>1,\<sigma>\<^sub>0,\<sigma>\<^sub>1,R,T)" "(W\<^sub>0',W\<^sub>1',\<sigma>\<^sub>0',\<sigma>\<^sub>1',R',T')"
    for W\<^sub>0 W\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1 R T W\<^sub>0' W\<^sub>1' \<sigma>\<^sub>0' \<sigma>\<^sub>1' R' T',
  where P="\<lambda>(a,b,c,d,e,f) (g,h,i,j,k,l). P a b c d e f g h i j k l"
    for P,
  unfolded split]

definition solve_step_I :: "'v solve_state \<Rightarrow> bool" where
  "solve_step_I \<equiv> \<lambda>(W\<^sub>0,W\<^sub>1,\<sigma>\<^sub>0,\<sigma>\<^sub>1,R,T).
    valid_subgame R \<and> winning_region EVEN W\<^sub>0 \<and> winning_region ODD W\<^sub>1 \<and> finite T \<and>
    (\<forall>t\<in>T. tangle EVEN t \<or> tangle ODD t) \<and> (\<forall>t\<in>T. \<forall>\<alpha>. tangle \<alpha> t \<longrightarrow> E `` (t\<inter>V_opponent \<alpha>)-t\<noteq>{})"

lemma valid_subgame_Un:
  "\<lbrakk>valid_subgame R; valid_subgame R'\<rbrakk> \<Longrightarrow> valid_subgame (R\<union>R')"
  apply clarsimp
  apply (unfold_locales; clarsimp)
  subgoal by blast
  subgoal for v using succ[of v] oops
  subgoal by blast
  done

lemma "\<lbrakk>solve_step (W\<^sub>0,W\<^sub>1,\<sigma>\<^sub>0,\<sigma>\<^sub>1,R,T) (W\<^sub>0',W\<^sub>1',\<sigma>\<^sub>0',\<sigma>\<^sub>1',R',T'); valid_subgame R\<rbrakk>
        \<Longrightarrow> R' \<subseteq> R"
  by (induction rule: solve_step_induct) auto

lemma solve_step_R_notempty:
  "solve_step (W\<^sub>0,W\<^sub>1,\<sigma>\<^sub>0,\<sigma>\<^sub>1,R,T) (W\<^sub>0',W\<^sub>1',\<sigma>\<^sub>0',\<sigma>\<^sub>1',R',T') \<Longrightarrow> R \<noteq> {}"
  by (induction rule: solve_step_induct) blast

definition solve :: "'v set \<Rightarrow> 'v set \<Rightarrow> 'v strat \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "solve W\<^sub>0 W\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<equiv> \<exists>T. solve_step\<^sup>*\<^sup>* ({},{},Map.empty,Map.empty,V,{}) (W\<^sub>0,W\<^sub>1,\<sigma>\<^sub>0,\<sigma>\<^sub>1,{},T)"

lemma solve_terminates_on_empty_R: "\<not>Domainp solve_step (W\<^sub>0,W\<^sub>1,\<sigma>\<^sub>0,\<sigma>\<^sub>1,{},T)"
  using solve_step_R_notempty by fast


lemma tanglelearning_terminates:
  "\<exists>W\<^sub>0 W\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1. solve W\<^sub>0 W\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1"
  oops

(** TODO: Redefine winning_region to also take a strategy, so we can say that the two strategies
    are also winning strategies. *)
lemma tanglelearning_partially_correct:
  "solve W\<^sub>0 W\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<Longrightarrow>
    V = W\<^sub>0 \<union> W\<^sub>1 \<and> W\<^sub>0 \<inter> W\<^sub>1 = {} \<and>
    winning_region EVEN W\<^sub>0 \<and>
    winning_region ODD W\<^sub>1"
  oops

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