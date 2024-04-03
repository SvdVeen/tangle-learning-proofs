theory StrongConnectivity
  imports Main Digraphs
begin
(**
  Authors:
    - Suzanne van der Veen
    - Peter Lammich
    - Tom van Dijk

  This theory focuses on strongly connected graphs and strongly connected components.
*)
chapter \<open>Strong Connectivity\<close>
section \<open>Strongly Connected Graphs\<close>
(** A non-empty graph E with vertices V is strongly connected if for all pairs of vertices in the
    graph, there exists a path from one to the other and vice-versa.
    We do not have to specify the path from v' to v, as it follows from the definition. *)
definition strongly_connected :: "'v dgraph \<Rightarrow> 'v set \<Rightarrow> bool" where
  "strongly_connected E V \<equiv> V \<noteq> {} \<and> E \<subseteq> V\<times>V \<and> (\<forall>v\<in>V. \<forall>v'\<in>V. (v,v') \<in> E\<^sup>*)"

(** An empty graph is not strongly connected. *)
lemma strongly_connected_notempty[simp]:
  "\<not>strongly_connected E {}"
  unfolding strongly_connected_def by blast

(** The edges in a strongly connected graph must include all vertices in V. *)
lemma strongly_connected_E_in_V: "strongly_connected E V \<Longrightarrow> E \<subseteq> V\<times>V"
  unfolding strongly_connected_def by blast

(** If a graph is strongly connected, there exists a path from every node to every other node. *)
lemma strongly_connected_path:
  "strongly_connected E V \<Longrightarrow> \<forall>v\<in>V. \<forall>v'\<in>V. \<exists>vs. path E v vs v'"
  unfolding strongly_connected_def
  using rtrancl_is_path[of _ _ E] by simp

(** If we restrict the graph to a cycle, we get a strongly connected graph. *)
lemma cycle_strongly_connected:
  "cycle E y ys \<Longrightarrow> strongly_connected (Restr E (set ys)) (set ys)"
  unfolding strongly_connected_def
proof (intro conjI)
  assume cycle: "cycle E y ys"
  (** Cycles are never empty *)
  thus "set ys \<noteq> {}" by auto
  (** This is trivially true for any restricted graph. *)
  show "Restr E (set ys) \<subseteq> set ys \<times> set ys" by blast
  (** Now, every node is reachable from each other node. *)
  show "\<forall>v\<in>set ys. \<forall>v'\<in>set ys. (v,v') \<in> (Restr E (set ys))\<^sup>*"
  proof (intro ballI)
    fix v v'
    assume v_in_ys: "v \<in> set ys"
       and v'_in_ys: "v' \<in> set ys"
    (** We can get a cycle from v. *)
    then obtain ys' where
      "set ys' = set ys" "cycle E v ys'"
      using cycle_intermediate_node[OF cycle] by auto
    (** Because v' is part of ys, there is now a path from v to v'. *)
    with v'_in_ys obtain vs where
      "path E v vs v'" "set vs \<subseteq> set ys"
      using path_intermediate_node[of E v ys' v v']
      by (clarsimp simp: cycle_def) blast
    (** Since this path is part of the cycle, it exists in the graph
        restricted to the cycle. *)
    from path_restr_V[OF this v'_in_ys]
    show "(v,v') \<in> (Restr E (set ys))\<^sup>*"
      using path_iff_rtrancl by fast
  qed
qed

context finite_graph_V
begin

section\<open>Strongly Connected Graphs Restricted to a Region\<close>
(** If a restricted graph is strongly connected, then every node in the
    region is reachable from every other node in the region. *)
lemma strongly_connected_connected:
  "\<lbrakk>R \<subseteq> V; strongly_connected (Restr E R) R\<rbrakk> \<Longrightarrow> \<forall>v\<in>R. \<forall>v'\<in>R. (v, v') \<in> E\<^sup>*"
  unfolding strongly_connected_def
  apply (simp add: path_iff_rtrancl)
  using path_inter(1) by metis

lemma strongly_connected_restr_connected:
  "\<lbrakk>R \<subseteq> V; strongly_connected (Restr E R) R\<rbrakk> \<Longrightarrow> \<forall>v\<in>R. \<forall>v'\<in>R. (v, v') \<in> (Restr E R)\<^sup>*"
  unfolding strongly_connected_def by blast

section \<open>Strongly Connected Components\<close>
(** A component in a graph is strongly connected when the graph restricted to that component is
    strongly connected and maximal; there is no larger component that contains it and is also
    strongly connected. *)
definition SCC :: "'v set \<Rightarrow> bool" where
  "SCC R \<equiv> R \<subseteq> V \<and> strongly_connected (Restr E R) R \<and>
    (\<nexists>R'. R \<subset> R' \<and> strongly_connected (Restr E R') R')"

(** SCCs are non-empty because our strong connectivity definition excludes empty graphs. *)
lemma SCC_notempty[simp]: "\<not>SCC {}"
  unfolding SCC_def by fastforce

(** All strongly connected components are subsets of V. *)
lemma SCC_in_V: "SCC R \<Longrightarrow> R \<subseteq> V"
  unfolding SCC_def by simp

(** Strongly connected components are finite sets. *)
lemma SCC_finite: "SCC R \<Longrightarrow> finite R"
  using finite_subset[OF SCC_in_V fin_V] .

(** The graph restricted to a strongly connected component is strongly connected. *)
lemma SCC_strongly_connected: "SCC R \<Longrightarrow> strongly_connected (Restr E R) R"
  unfolding SCC_def by blast

(** Strongly connected components are maximal. *)
lemma SCC_maximal: "SCC R \<Longrightarrow> \<nexists>R'. R \<subset> R' \<and> strongly_connected (Restr E R') R'"
  unfolding SCC_def by blast

lemma SCC_maximal': "SCC R \<Longrightarrow> \<nexists>R'. R \<subset> R' \<and> SCC R'"
  using SCC_in_V SCC_strongly_connected
  using strongly_connected_connected
  using SCC_maximal[of R]
  by metis

(** For every pair of nodes in a strongly connected component, there exists a path from one to the
    other. *)
lemma SCC_path: "SCC R \<Longrightarrow> \<forall>v\<in>R. \<forall>v'\<in>R. \<exists>vs. path (Restr E R) v vs v'"
  unfolding SCC_def using strongly_connected_path[of "Restr E R" R] by blast

(** If there is a nonempty region in V that is strongly connected, then either it is an SCC itself,
    or it is part of a larger SCC. *)
lemma maximal_SCC_candidate:
  assumes R_notempty: "R \<noteq> {}"
  assumes R_in_V: "R \<subseteq> V"
  assumes conn: "strongly_connected (Restr E R) R"
  shows "\<exists>R'. R \<subseteq> R' \<and> SCC R'"
proof -
  (** We get the set of all nodes that are reachable from R. *)
  define R' where "R' \<equiv> {x | x y. (x \<in> R \<or> y \<in> R) \<and> (x,y) \<in> E\<^sup>* \<and> (y,x) \<in> E\<^sup>*}"
  (** This is clearly a nonempty subset of V, that may be equal to R. *)
  have "R \<subseteq> R'" unfolding R'_def by blast
  moreover from R_notempty have "R' \<noteq> {}" unfolding R'_def by blast
  moreover from R_in_V have "R' \<subseteq> V" unfolding R'_def
    using trancl_subset_Sigma_aux[OF _ E_in_V] by blast
  (** R' is now strongly connected. *)
  moreover have "strongly_connected (Restr E R') R'"
  proof -
    {
      fix v v' assume "v \<in> R'" "v' \<in> R'"
      (** Every node in R' is reachable from every other node in R' because of the way it was
          defined. *)
      from conn have R'_conn:
        "\<forall>v \<in> R'. \<forall>v'\<in>R'. (v,v') \<in> E\<^sup>*"
        unfolding strongly_connected_def R'_def
        using rtrancl_trans[of _ _ E] path_inter[of E "R\<times>R"]
        by (simp add: path_iff_rtrancl) metis
      (** Therefore, our v and v' are reachable from one another. *)
      with \<open>v\<in>R'\<close> \<open>v'\<in>R'\<close> have "(v,v')\<in>E\<^sup>*" "(v',v)\<in>E\<^sup>*"
        by blast+
      (** This means we can get a path between each, and we can append those two to get a path
          from v to v. *)
      then obtain xs ys where
        path_xs: "path E v xs v'" and
        path_ys: "path E v' ys v"
        by (auto simp: path_iff_rtrancl)
      hence path: "path E v (xs@ys) v" by auto
      (** This path stays in R'. We prove this by contradiction. *)
      have "set (xs@ys) \<subseteq> R'" proof (rule ccontr)
        (** Because the path doesn't stay in R', there must exist a w in the path that is part of
            V-R'. *)
        assume "\<not>set (xs@ys) \<subseteq> R'"
        with path obtain w where
          "w \<in> set (xs@ys)" "w \<in> V-R'"
          using path_in_V by blast
        (** We can get a path from this node to v, and from v to this node.
            This means the two are reachable from one another. *)
        from path_intermediate_node[OF path this(1)]
        obtain vs ws where
          "path E v vs w" "path E w ws v" by blast
        hence "(v,w) \<in> E\<^sup>*" "(w,v) \<in> E\<^sup>*"
          by (auto simp: path_iff_rtrancl)
        (** This would mean that adding w to R' would make another connected region. *)
        with R'_conn \<open>v\<in>R'\<close> have
          "\<forall>v\<in>insert w R'. \<forall>v'\<in>insert w R'. (v,v') \<in> E\<^sup>*"
          by fastforce
        (** But the way we defined R' means that w should already have been part of R' in that case.
            This gives us a contradiction, showing that the path from v to v stays in R'. *)
        with \<open>R\<noteq>{}\<close> \<open>w\<in>V-R'\<close> show False
          using R'_def by blast
      qed
      (** Therefore, the path from v to v' stays in R', thus v is reachable from v' in the graph
          restricted to R'. *)
      hence "set xs \<subseteq> R'" by auto
      from path_restr_V[OF path_xs this \<open>v'\<in>R'\<close>]
      have "(v,v') \<in> (Restr E R')\<^sup>*"
        by (auto simp: path_iff_rtrancl)
    }
    (** Now, because R' is not empty, and all nodes in R' are reachable in the restricted graph,
        this restricted graph is strongly connected. *)
    with \<open>R'\<noteq>{}\<close> show ?thesis
      unfolding strongly_connected_def by simp
  qed
  (** Furthermore, there is no larger S containing R' that is also strongly connected.
      We prove this by contradiction . *)
  moreover have "\<nexists>S. R' \<subset> S \<and> strongly_connected (Restr E S) S"
  proof
    (** We obtain the S that contains R' and is strongly connected. *)
    assume "\<exists>S. R' \<subset> S \<and> strongly_connected (Restr E S) S"
    then obtain S where
      "R' \<subset> S" "strongly_connected (Restr E S) S"
      by blast
    (** This means that all nodes in S are reachable from all other nodes in S. *)
    hence "\<forall>v\<in>S. \<forall>v'\<in>S. (v,v') \<in> E\<^sup>*"
      unfolding strongly_connected_def
      apply (simp add: path_iff_rtrancl)
      using path_inter(1) by meson
    (** However, this is a contradiction, because they would have been part of R'. *)
    with \<open>R'\<subset>S\<close> \<open>R \<noteq>{}\<close> show False
      unfolding R'_def by blast
  qed
  (** Toghether, the former properties show that either R is an SCC, or there exists an R' which
      contains R that is an SCC. *)
  ultimately show ?thesis
    unfolding SCC_def by blast
qed

(** All nodes in V are part of an SCC. *)
lemma all_v_in_SCC:
  assumes v_in_V: "v \<in> V"
  shows "\<exists>R. v \<in> R \<and> SCC R"
  apply (rule ccontr)
  using assms maximal_SCC_candidate[of "{v}"]
  unfolding strongly_connected_def by blast

(** There alway exists an SCC if the graph is not empty. *)
lemma SCC_ex:
  assumes "V \<noteq> {}"
  shows "\<exists>R. SCC R"
  using assms all_v_in_SCC
  by blast

(** Thet set of all SCCs. *)
definition SCCs :: "'v set set" where
  "SCCs \<equiv> {R. SCC R}"

(** The set of SCCs is not empty if the graph is not empty. *)
lemma SCCs_notempty:
  assumes "V\<noteq>{}"
  shows "SCCs \<noteq> {}"
  using SCC_ex[OF assms]
  unfolding SCCs_def
  by simp

(** There are a finite number of SCCs in every graph. *)
lemma finite_SCCs[simp]: "finite SCCs"
  unfolding SCCs_def SCC_def by fast


section \<open>Bottom Strongly Connected Components\<close>
(** A bottom SCC is a strongly connected component where there exist no edges from the SCC to the
    region outside of it; the SCC is closed. *)
definition bottom_SCC :: "'v set \<Rightarrow> bool" where
  "bottom_SCC R \<equiv> SCC R \<and> E `` R \<subseteq> R"

(** Bottom SCCs are strongly connected components. *)
lemma bottom_SCC_is_SCC: "bottom_SCC R \<Longrightarrow> SCC R"
  unfolding bottom_SCC_def by simp

(** Bottom SCCs are not empty because strongly connected components are not empty by our definition *)
lemma bottom_SCC_notempty[simp]: "\<not>bottom_SCC {}"
  using bottom_SCC_is_SCC by force

(** Bottom SCCs exist within the graph. *)
lemma bottom_SCC_in_V: "bottom_SCC R \<Longrightarrow> R \<subseteq> V"
  using SCC_in_V[OF bottom_SCC_is_SCC] .

(** Bottom SCCs are finite. *)
lemma bottom_SCC_finite: "bottom_SCC R \<Longrightarrow> finite R"
  using finite_subset[OF bottom_SCC_in_V fin_V] .

(** The graph restricted to a bottom SCC is strongly connected. *)
lemma bottom_SCC_strongly_connected:
  "bottom_SCC R \<Longrightarrow> strongly_connected (Restr E R) R"
  using SCC_strongly_connected[OF bottom_SCC_is_SCC] .

(** All bottom SCCs are maximal. *)
lemma bottom_SCC_maximal:
  "bottom_SCC R \<Longrightarrow> \<nexists>R'. R \<subset> R' \<and> strongly_connected (Restr E R') R'"
  using SCC_maximal[OF bottom_SCC_is_SCC] .

(** Bottom SCCs are closed in E. *)
lemma bottom_SCC_closed: "bottom_SCC R \<Longrightarrow> E `` R \<subseteq> R"
  unfolding bottom_SCC_def by simp

(** For every pair of nodes in a strongly connected component, there exists a path from one to the
    other. *)
lemma bottom_SCC_path: "bottom_SCC R \<Longrightarrow> \<forall>v\<in>R. \<forall>v'\<in>R. \<exists>vs. path (Restr E R) v vs v'"
  using SCC_path[OF bottom_SCC_is_SCC] by blast

(** The set of all bottom SCCs. *)
definition bottom_SCCs :: "'v set set" where
  "bottom_SCCs \<equiv> {R. bottom_SCC R}"

(** The set of all bottom SCCs is a subset of the set of all SCCs. *)
lemma bottom_SCCs_subset_SCCs:
  "bottom_SCCs \<subseteq> SCCs"
  unfolding bottom_SCCs_def SCCs_def
  using bottom_SCC_is_SCC by blast

(** There are a finite number of bottom SCCs in the graph. *)
lemma finite_bottom_SCCs[simp]:
  "finite bottom_SCCs"
  using finite_subset[OF bottom_SCCs_subset_SCCs]
  by simp


section \<open>Non-trivial Bottom SCCs\<close>
(** Non-trivial bottom SCCs are those that contain at least one edge within them. *)
definition nt_bottom_SCC :: "'v set \<Rightarrow> bool" where
  "nt_bottom_SCC R \<equiv> bottom_SCC R \<and> (Restr E R) \<noteq> {}"

(** A non-trivial bottom SCC is a bottom SCC. *)
lemma nt_bottom_SCC_is_bottom_SCC: "nt_bottom_SCC R \<Longrightarrow> bottom_SCC R"
  unfolding nt_bottom_SCC_def by simp

(** A non-trivial bottom SCC is a strongly connected component. *)
lemma nt_bottom_SCC_is_SCC: "nt_bottom_SCC R \<Longrightarrow> SCC R"
  using bottom_SCC_is_SCC[OF nt_bottom_SCC_is_bottom_SCC] .

(** A non-trivial bottom SCC is not empty. *)
lemma nt_bottom_SCC_notempty[simp]: "\<not>nt_bottom_SCC {}"
  using nt_bottom_SCC_is_bottom_SCC by force

(** A non-trivial bottom SCC exists within the graph. *)
lemma nt_bottom_SCC_in_V: "nt_bottom_SCC R \<Longrightarrow> R \<subseteq> V"
  using SCC_in_V[OF nt_bottom_SCC_is_SCC] .

(** Non-trivial bottom SCCs are finite. *)
lemma nt_bottom_SCC_finite: "nt_bottom_SCC R \<Longrightarrow> finite R"
  using finite_subset[OF nt_bottom_SCC_in_V fin_V] .

(** The graph restricted to a non-trivial bottom SCC is strongly connected. *)
lemma nt_bottom_SCC_strongly_connected: "nt_bottom_SCC R \<Longrightarrow> strongly_connected (Restr E R) R"
  using SCC_strongly_connected[OF nt_bottom_SCC_is_SCC] .

(** Non-trivial bottom SCCs are maximal. *)
lemma nt_bottom_SCC_maximal:
  "nt_bottom_SCC R \<Longrightarrow> \<nexists>R'. R \<subset> R' \<and> strongly_connected (Restr E R') R'"
  using SCC_maximal[OF nt_bottom_SCC_is_SCC] .

(** A non-trivial bottom SCC has at least one edge. *)
lemma nt_bottom_SCC_has_edge: "nt_bottom_SCC R \<Longrightarrow> (Restr E R) \<noteq> {}"
  unfolding nt_bottom_SCC_def by blast

(** Non-trivial bottom SCCs cannot consist of a single node without a self-loop. *)
lemma nt_bottom_SCC_nontrivial: "(v,v) \<notin> E \<Longrightarrow> \<not>nt_bottom_SCC {v}"
  unfolding nt_bottom_SCC_def by fast

(** A non-trivial bottom SCC is closed. *)
lemma nt_bottom_SCC_closed: "nt_bottom_SCC R \<Longrightarrow> E `` R \<subseteq> R"
  using bottom_SCC_closed[OF nt_bottom_SCC_is_bottom_SCC] .

(** For every pair of nodes in a non-trivial bottom SCC, there exists a path from one node to the
    other. *)
lemma nt_bottom_SCC_path: "nt_bottom_SCC R \<Longrightarrow> \<forall>v\<in>R. \<forall>v'\<in>R. \<exists>vs. path (Restr E R) v vs v'"
  using SCC_path[OF nt_bottom_SCC_is_SCC] .

(** In a non-trivial bottom SCC, every node in the SCC has a successor that also exists in the SCC. *)
lemma nt_bottom_SCC_succ_in_SCC:
  "\<lbrakk>nt_bottom_SCC R; v\<in>R\<rbrakk> \<Longrightarrow> \<exists>v'\<in>R. (v,v')\<in>E"
proof -
  assume SCC_R: "nt_bottom_SCC R" and v_in_R: "v \<in> R"
  from SCC_R have R_in_V: "R \<subseteq> V"
    using nt_bottom_SCC_in_V by auto
  consider (loop) "(v,v) \<in> E" | (no_loop) "(v,v) \<notin> E" by blast
  thus "\<exists>v'\<in>R. (v,v') \<in> E" proof cases
    (** If there is a self loop, the successor of v in R is v itself. *)
    case loop with v_in_R show ?thesis by fast
  next
    case no_loop
    (** Because the bottom SCC is non-trivial, without a self loop from v, there  must exist another
        node v' in R that is not v. *)
    from nt_bottom_SCC_nontrivial[OF this] SCC_R have "R\<noteq>{v}" by auto
    with v_in_R  obtain v' where
      v'_in_R: "v' \<in> R" and v'_not_v: "v' \<noteq> v"
      by blast
    (** Because the component is strongly connected, we can obtain a path from v to v',  which is
        not empty because v and v' are not the same node. *)
    from nt_bottom_SCC_path[OF SCC_R] v_in_R v'_in_R v'_not_v obtain vs where
      restr_path_v_vs_v': "path (Restr E R) v vs v'" and
      vs_notempty: "vs \<noteq> []"
      by force
    (** This path exists in the whole graph, but all nodes within it are nodes in R. *)
    from restr_V_path[OF this] have
      vs_in_R: "set vs \<subseteq> R" and path_v_vs_v': "path E v vs v'" by blast+
    (** Now we can get the next node w in the path from v to v'. *)
    with v'_in_R obtain w ws where
      ws_in_vs: "vs = v#ws" and w_succ_v: "(v,w) \<in> E" and path_w_ws_v': "path E w ws v'"
      using path_D[OF path_v_vs_v' vs_notempty] by blast
    (** This node is in R because the whole path is in R.  *)
    with v'_in_R vs_in_R have w_in_R: "w\<in>R"
      using origin_in_path[OF path_w_ws_v'] by fastforce
    (** Now we can use w as the successor of v in R. *)
    with w_succ_v show ?thesis by blast
  qed
qed

(** For every pair of nodes in a non-trivial bottom SCC, there exists a non-empty path from one node
    to the other.  *)
lemma nt_bottom_SCC_path_nonempty:
  "nt_bottom_SCC R \<Longrightarrow> \<forall>v\<in>R. \<forall>v'\<in>R. \<exists>vs. vs \<noteq> [] \<and> path (Restr E R) v vs v'"
proof (intro ballI)
  fix v v'
  assume SCC_R: "nt_bottom_SCC R" and v_in_R: "v \<in> R" and v'_in_R: "v' \<in> R"
  from SCC_R have R_in_V: "R \<subseteq> V" and R_connected: "strongly_connected (Restr E R) R"
    using nt_bottom_SCC_in_V nt_bottom_SCC_strongly_connected by blast+
  (** Because R is strongly connected, we know there is a path from v to v' in the reflexive
      transitive closure of E restricted to R. We can use an induction over this to show our thesis. *)
  from strongly_connected_restr_connected[OF this] v_in_R v'_in_R
  have "(v,v') \<in> (Restr E R)\<^sup>*" by simp
  thus "\<exists>vs. vs \<noteq> [] \<and> path (Restr E R) v vs v'"
  proof (induction rule: converse_rtrancl_induct)
    case base
    (** We know that in a restricted subgraph that is strongly connected, each node has a successor
        in the restricted region. We take this successor and get the path from v' to w, which only
        consists of v' itself. *)
    from nt_bottom_SCC_succ_in_SCC[OF SCC_R v'_in_R]
    obtain w where w_in_R: "w \<in> R" and w_succ_v': "(v',w)\<in>E" by blast
    hence path_v_w: "path E v' [v'] w" by simp
    (** Now we get the (possibly empty) path from w back to v'. We prepend v', completing the loop. *)
    from nt_bottom_SCC_path[OF SCC_R] w_in_R v'_in_R obtain vs where
      path_w_vs_v': "path (Restr E R) w vs v'" by fast
    with w_succ_v' v'_in_R w_in_R have "path (Restr E R) v' (v'#vs) v'" by auto
    thus ?case by blast
  next
    (** In the step case, we already have a non-empty path between two nodes, and a predecessor of
        the start of that path. We just prepend the predecessor to complete the path from there to
        the destination. *)
    case (step y z) thus ?case by fastforce
  qed
qed

(** From every node in a non-trivial bottom SCC, there exists a cycle. *)
lemma nt_bottom_SCC_cycle: "nt_bottom_SCC R \<Longrightarrow> \<forall>v\<in>R. \<exists>ys. cycle (Restr E R) v ys"
proof (rule ballI)
  fix v
  assume SCC_R: "nt_bottom_SCC R" and v_in_R: "v\<in>R"
  (** We can take some other (not necessarily different) v' in R and get the non-empty path from
      v to v', append the path from v' to v, and we have a cycle. *)
  then obtain v' where v'_in_R: "v'\<in>R" by blast
  from nt_bottom_SCC_path_nonempty[OF SCC_R] v_in_R v'_in_R
  obtain vs1 vs2 where
    path_v_v': "path (Restr E R) v vs1 v'" and vs1_notempty: "vs1 \<noteq> []" and
    path_v'_v: "path (Restr E R) v' vs2 v" and vs2_notempty: "vs2 \<noteq> []"
    by blast
  hence "path (Restr E R) v (vs1@vs2) v" by auto
  with vs1_notempty vs2_notempty show "\<exists>ys. cycle (Restr E R) v ys"
    unfolding cycle_def by blast
qed

(** The set of all nontrivial bottom SCCs. *)
definition nt_bottom_SCCs :: "'v set set" where
  "nt_bottom_SCCs \<equiv> {R. nt_bottom_SCC R}"

(** The set of all nontrivial bottom SCCs is a subset of the set of all bottom SCCs. *)
lemma nt_bottom_SCCs_subset_bottom_SCCs:
  "nt_bottom_SCCs \<subseteq> bottom_SCCs"
  unfolding nt_bottom_SCCs_def bottom_SCCs_def
  using nt_bottom_SCC_is_bottom_SCC by blast

(** The set of all nontrivial bottom SCCs is a subset of the set of all SCCs. *)
lemma nt_bottom_SCCs_subset_SCCs:
  "nt_bottom_SCCs \<subseteq> SCCs"
  using nt_bottom_SCCs_subset_bottom_SCCs
  using bottom_SCCs_subset_SCCs
  by blast

(** There are a finite number of non-trivial bottom SCCs in the graph. *)
lemma finite_nt_bottom_SCCs[simp]:
  "finite nt_bottom_SCCs"
  using finite_subset[OF nt_bottom_SCCs_subset_SCCs]
  by simp


(** We will use the concept of a condensation to prove the existence of bottom SCCs. *)
section \<open>Condensations\<close>
(** The condensation of a graph is a graph of the contractions of each SCC.
    Each SCC is collapsed to a single node, and the edges are those between the SCCs.
    There are no self loops. If they did, then every SCC would have one, which is not useful.*)
definition condensation :: "'v set dgraph" where
  "condensation \<equiv>
    {(R,R') | R R' x y. R \<noteq> R' \<and> R \<in> SCCs \<and> R' \<in> SCCs \<and> x \<in> R \<and> y \<in> R' \<and> (x,y) \<in> E}"

(** By their definition, condensations do not contain self loops. *)
lemma condensation_no_self_loops[simp]:
  "(R,R) \<notin> condensation"
  unfolding condensation_def by blast

(** If a region is a subset of another, then a node reachable in the graph restricted to the small
    region is also reachable in the graph restricted to the larger region. *)
lemma Restr_subgraph_aux:
  "\<lbrakk>R \<subseteq> R'; (x,y) \<in> (Restr E R)\<^sup>*\<rbrakk> \<Longrightarrow> (x,y) \<in> (Restr E R')\<^sup>*"
  using Restr_subset[of R R'] rtrancl_mono[of "Restr E R" "Restr E R'"]
  by blast

(** A condensation is a finite graph with all SCCs as its nodes. *)
lemma condensation_finite_graph_V:
  "finite_graph_V condensation SCCs"
  by (unfold_locales) (auto simp: condensation_def)

(** If an edge exists in the condensation, then there exists an edge between the two SCCs, and they
    are not the same. This holds in both directions. *)
lemma edge_in_condensation_iff:
  "(R,R') \<in> condensation \<longleftrightarrow> R \<noteq> R' \<and> SCC R \<and> SCC R' \<and> (\<exists>x\<in>R. \<exists>y\<in>R'. (x,y) \<in> E)"
  unfolding condensation_def SCCs_def by auto

(** If there exists an edge between two SCCs in the condensation, then every node in the latter SCC
    is reachable from every node in the former SCC. *)
lemma condensation_edge_restr_reachable:
  "(R,R') \<in> condensation \<Longrightarrow> \<forall>x\<in>R. \<forall>y\<in>R'. (x,y) \<in> (Restr E (R\<union>R'))\<^sup>*"
proof (intro ballI)
  fix x y assume "x \<in> R" "y \<in> R'" and c_edge: "(R,R') \<in> condensation"
  (** We get the edge between the two SCCs. *)
  then obtain v w where
    "SCC R" "SCC R'" "v \<in> R" "w \<in> R'" and edge_vw: "(v,w) \<in> (Restr E (R\<union>R'))"
    using edge_in_condensation_iff by auto
  (** We know we can reach v from our x in R, and this is also reachable if we restrict
      the whole graph to only our two SCCs. *)
  from \<open>SCC R\<close> \<open>x\<in>R\<close> \<open>v\<in>R\<close> have reach_xv: "(x,v) \<in> (Restr E (R\<union>R'))\<^sup>*"
    using SCC_strongly_connected SCC_in_V
    using strongly_connected_restr_connected[of R]
    using Restr_subgraph_aux[of R "R\<union>R'"] by auto
  (** The same holds for our y in R', which can be reached from w. *)
  from \<open>SCC R'\<close> \<open>w\<in>R'\<close> \<open>y\<in>R'\<close> have reach_wy: "(w,y) \<in> (Restr E (R\<union>R'))\<^sup>*"
    using SCC_strongly_connected SCC_in_V
    using strongly_connected_restr_connected[of R']
    using Restr_subgraph_aux[of R' "R\<union>R'"] by auto
  (** Now, we can reach v from x, w, from v, and y from w, all in the graph restricted to our
      SCCs. *)
  from reach_xv edge_vw reach_wy show "(x,y) \<in> (Restr E (R\<union>R'))\<^sup>*"
    using rtrancl_trans[of _ _ "Restr E (R\<union>R')"] by blast
qed

(** All nodes in a path in the condensation are SCCs in the whole graph. *)
lemma condensation_path_SCCs:
  "\<lbrakk>path condensation R rs R'; SCC R\<rbrakk> \<Longrightarrow> (\<forall>r\<in>set rs. SCC r) \<and> SCC R'"
  using finite_graph_V.path_in_V[OF condensation_finite_graph_V]
  using finite_graph_V.path_closed_V[OF condensation_finite_graph_V]
  unfolding SCCs_def by blast

(** From all nodes in the SCC at the start of a path in the condensation, all nodes in the SCCs in
    the path can be reached within the graph restricted to those SCCs. *)
lemma condensation_path_restr_reachable:
  "\<lbrakk>path condensation R rs R'; SCC R\<rbrakk>
    \<Longrightarrow> \<forall>x\<in>R. \<forall>y\<in>\<Union>(set rs) \<union> R'. (x,y) \<in> (Restr E (\<Union>(set rs) \<union> R'))\<^sup>*"
proof (induction rs arbitrary: R)
  (** In the Nil case, we only have to reason about the initial R.
      Clearly this SCC is stronly connected, so all nodes in it are reachable from it. *)
  case Nil thus ?case
    using SCC_strongly_connected SCC_in_V
    by (simp add: strongly_connected_restr_connected)
next
  (** In the cons case, we know R is one of the SCCs, and that it is a subset
      of the union of all SCCs in the path and R'. *)
  case (Cons r rs)
  from \<open>SCC R\<close> have "R \<in> SCCs"
    unfolding SCCs_def by blast
  from Cons have subset_1: "R \<subseteq> (\<Union>(set (r#rs)) \<union> R')"
    using origin_in_path by auto
  (** Now, we know there is a path from some r' over rs to R'. *)
  from Cons obtain r' where
    path: "path condensation r' rs R'" and
    cons_edge: "(R,r')\<in>condensation"
    by auto
  (** We see that the union of this and R are part of the union of all SCCs
      in the path and R'. *)
  with subset_1 have subset_2: "R\<union>r' \<subseteq> (\<Union>(set (r#rs)) \<union> R')"
    using origin_in_path by fastforce
  (** Furthermore, the union of all SCCs in the path except r and R' is part of the
      union of all SCCs in the pth and R'. *)
  have subset_3: "(\<Union> (set rs) \<union> R') \<subseteq> (\<Union>(set (r#rs)) \<union> R')"
    by (simp add: Un_assoc)
  (** We know that all y in r' are reachable from all x in R, restricting the graph
      to the union of all SCCs in the path and R'. *)
  from cons_edge have r'_reach:
    "\<forall>x\<in>R. \<forall>y\<in>r'. (x, y) \<in> (Restr E (\<Union>(set (r#rs)) \<union> R'))\<^sup>*"
    using condensation_edge_restr_reachable
    using Restr_subgraph_aux[OF subset_2] by blast
  (** Also, we know that R alone forms a path from R to r' in the condensation. *)
  from cons_edge have "path condensation R [R] r'" by auto
  (** This shows that r' is an SCC, since all elements of a path in the
      condensation are SCCs. *)
  from condensation_path_SCCs[OF this \<open>SCC R\<close>]
  have "SCC r'" unfolding SCCs_def by simp
  (** By our induction hypothesis, we know that every y in the union of all SCCs
      in rs and R' can be reached from r'. *)
  from Cons.IH[OF path this] have r'_reaches:
    "\<forall>x\<in>r'. \<forall>y\<in>\<Union> (set rs) \<union> R'. (x, y) \<in> (Restr E (\<Union>(set (r#rs)) \<union> R'))\<^sup>*"
    using Restr_subgraph_aux[OF subset_3] by blast

  show ?case
  proof (intro ballI)
    fix x y assume "x \<in> R" "y \<in> \<Union>(set (r#rs)) \<union> R'"
    (** Because r#rs forms a path from r, this means r is equal to R. *)
    with Cons(2) have "y \<in> \<Union>(set (R#rs)) \<union> R'" by auto
    (** Now, we can see y is either part of R, or it is part of the remainder of
        the SCCs in the path or R'. *)
    then consider (in_R) "y \<in> R" | (in_rs_R') "y \<in> \<Union>(set rs) \<union> R'" by fastforce
    thus "(x,y) \<in> (Restr E (\<Union> (set (r # rs)) \<union> R'))\<^sup>*" proof cases
      (** If y is part of R, then we have the same reasoning as the Nil case.
          R is an SCC, so y is reachable from any node in R, even if we restrict
          the graph to the SCCs in our path. *)
      case in_R with \<open>x\<in>R\<close> \<open>SCC R\<close> show ?thesis
        using SCC_strongly_connected SCC_in_V
        using strongly_connected_restr_connected
        using Restr_subgraph_aux[OF subset_1]
        by simp
    next
      (** If y is part of the rest of the path, then we get a z in r'. *)
      case in_rs_R'
      from \<open>SCC r'\<close> obtain z where "z \<in> r'" by force
      (** This z is reachable from x, even if we restrict the graph to
          all SCCs in our path. *)
      with \<open>x\<in>R\<close> r'_reach have
        "(x,z) \<in> (Restr E (\<Union>(set (r#rs)) \<union> R'))\<^sup>*" by blast
      (** Also, we showed that any node in the remainder can be reached
          from any node in r', so y can be reached from z, even in the
          restricted graph. *)
      moreover from \<open>z\<in>r'\<close> in_rs_R' r'_reaches
      have "(z,y) \<in> (Restr E (\<Union>(set (r#rs)) \<union> R'))\<^sup>*" by blast
      (** Now, we can reach y from x via z in the restricted graph. *)
      ultimately show ?thesis by simp
    qed
  qed
qed

(** If we have a loop in the condensation, then this loop is non-empty.
    This holds because there are no self loops in the condensation. *)
lemma condensation_loop_notempty:
  "\<lbrakk>path condensation R rs R; rs \<noteq> []\<rbrakk> \<Longrightarrow> \<exists>R'. R'\<noteq>R \<and> R' \<in> set rs"
  using origin_in_path[of condensation _ _ R] edge_in_condensation_iff[of R R]
  by (induction rs) fastforce+

(** All nodes in a loop in the condensation are SCCs. *)
lemma condensation_loop_SCCs:
  "\<lbrakk>path condensation R rs R; rs \<noteq> []\<rbrakk> \<Longrightarrow> \<forall>r \<in> set rs. SCC r"
  apply (induction rs; clarsimp)
  using edge_in_condensation_iff condensation_path_SCCs by metis

(** All nodes in an SCC in a loop in the condensation are reachable from
    all other nodes in any SCC in that loop. *)
lemma condensation_loop_restr_reachable:
  "\<lbrakk>path condensation R rs R; rs \<noteq> []\<rbrakk>
    \<Longrightarrow> \<forall>x\<in>\<Union>(set rs). \<forall>y\<in>\<Union>(set rs). (x,y) \<in> (Restr E (\<Union>(set rs)))\<^sup>*"
proof (intro ballI)
  fix x y
  assume x_UN: "x \<in> \<Union>(set rs)" and y_UN: "y \<in> \<Union>(set rs)"
     and path: "path condensation R rs R" and "rs \<noteq> []"
  (** All nodes in the loop are SCCs. *)
  from condensation_loop_SCCs[OF path \<open>rs\<noteq>[]\<close>]
  have rs_SCCs: "\<forall>r \<in> set rs. SCC r" .
  (** We get the SCC x is part of and the SCC y is part of. *)
  from x_UN obtain S where "x \<in> S" and S_in_rs: "S \<in> set rs" by blast
  with rs_SCCs have "SCC S" by blast
  from y_UN obtain S' where "y \<in> S'" and S'_in_rs: "S' \<in> set rs" by blast
  with rs_SCCs have "SCC S'" by blast
  (** now, we can get a path from S to itself. *)
  from loop_intermediate_node[OF path S_in_rs] obtain rs' where
    "set rs' = set rs" "path condensation S rs' S" by blast
  (** Within this path, we can get the path from  S to S', because
      S' is part of the path from S to S. *)
  with path_intermediate_node S'_in_rs obtain rs'' where
    "set rs'' \<subseteq> set rs" and rs''_path: "path condensation S rs'' S'"
    by (metis Un_upper1 set_append)
  (** The union of this path and S' are a subset of the union of the
      original rs. *)
  with S'_in_rs have "(\<Union>(set rs'') \<union> S') \<subseteq> \<Union>(set rs)" by blast
  (** By our earlier lemma, this means y must be reachable from x
      in the graph restricted to the SCCs inour path. *)
  with condensation_path_restr_reachable[OF rs''_path \<open>SCC S\<close>] \<open>x \<in> S\<close> \<open>y \<in> S'\<close>
  show "(x, y) \<in> (Restr E (\<Union>(set rs)))\<^sup>*"
    using Restr_subgraph_aux by blast
qed

corollary condensation_loop_reachable:
  "\<lbrakk>path condensation R rs R; rs \<noteq> []\<rbrakk>
    \<Longrightarrow> \<forall>x\<in>\<Union>(set rs). \<forall>y\<in>\<Union>(set rs). (x,y) \<in> E\<^sup>*"
  using condensation_loop_restr_reachable
  by (metis Int_Un_eq(3) in_rtrancl_UnI)

(** The condensation of a graph cannot contain any cycles. *)
lemma condensation_no_cycles:
  shows "\<not>cycle condensation R rs"
proof
  (** We do a proof by contradiction: if we have a cycle from R,
      then we have a nonempty path from R to R. *)
  assume cycle: "cycle condensation R rs"
  hence path: "path condensation R rs R" and "rs \<noteq> []"
    unfolding cycle_def by auto
  (** We know there must exist another SCC R' in this cycle. *)
  then obtain R' where R': "R \<noteq> R'" "R' \<in> set rs"
    using condensation_loop_notempty[of R] by blast
  (** Both are SCCs because they are part of the cycle. *)
  with cycle condensation_loop_SCCs
  have "SCC R" "SCC R'"
    using origin_in_cycle
    unfolding cycle_def by fast+
  (** This means neither of the two is empty, as SCCs are not empty. *)
  from \<open>SCC R\<close> \<open>SCC R'\<close> have not_empty:
    "R \<noteq> {}" "R' \<noteq> {}" by auto
  (**Also, neither is a strict subset of the other, as SCCs are maximal. *)
  from \<open>SCC R\<close> \<open>SCC R'\<close> have no_subsets:
    "\<not>R \<subset> R'" "\<not>R' \<subset> R"
    using SCC_maximal' by auto
  (** Now we take the union of all SCCs in the cycle.
      We will show that this would be another strongly connected region. *)
  define S where "S \<equiv> \<Union>(set rs)"
  (** R is now a strict subset of S. *)
  have "R \<subset> S"
  proof (rule psubsetI)
    (** Since R is part of the cycle, it is a subset of S. *)
    show "R \<subseteq> S"
      using origin_in_cycle[OF cycle]
      unfolding S_def by blast
    (** R' is also a subset of S, as it is part of the cycle. *)
    from R' have "R' \<subseteq> S"
      unfolding S_def by blast
    (** Since neither is empty, and neither is a strict subset
        of the other, R is not equal to S. *)
    with no_subsets not_empty \<open>R\<noteq>R'\<close> show "R \<noteq> S"
      unfolding S_def by auto
  qed
  (** Because this is a loop, the whole S is stronly connected. *)
  moreover from not_empty \<open>R' \<in> set rs\<close> have "strongly_connected (Restr E S) S"
    using condensation_loop_restr_reachable[OF path \<open>rs\<noteq>[]\<close>]
    unfolding strongly_connected_def S_def by blast
  (** Now, we have an S of which R is a strict subset, and which is strongly
      connected. This contradicts the fact that R should be maximal, as it is
      an SCC, completing our proof. *)
  ultimately show False
    using SCC_maximal[OF \<open>SCC R\<close>] by simp
qed

section \<open>Existence Of Bottom SCCs\<close>
(** In a finite graph, there always exists a bottom SCC. *)
lemma bottom_SCC_ex:
  assumes v_notempty: "V \<noteq> {}"
  shows "\<exists>R. bottom_SCC R"
proof (rule ccontr)
  assume no_bottom_SCC: "\<nexists>R. bottom_SCC R"
  (** Because there are no bottom SCCs, every SCC must have an edge to a different SCC. *)
  have SCC_succ: "\<forall>R. SCC R \<longrightarrow> (\<exists>R'. R'\<noteq>R \<and> SCC R' \<and> (\<exists>x\<in>R. \<exists>y\<in>R'. (x,y) \<in> E))"
  proof -
    (** Every SCC must have an edge leaving it. *)
    from no_bottom_SCC have "\<forall>R. SCC R \<longrightarrow> (\<exists>x\<in>R. \<exists>y. y \<notin> R \<and> (x,y) \<in> E)"
      unfolding bottom_SCC_def by blast
    (** Every SCC must have an edge to an SCC. *)
    moreover from no_bottom_SCC have "\<forall>R. SCC R \<longrightarrow> (\<exists>R'. SCC R' \<and> (\<exists>x\<in>R. \<exists>y\<in>R'. (x,y) \<in> E))"
      unfolding bottom_SCC_def
      using all_v_in_SCC E_in_V by blast
    (** Therefore, every SCC must have an edge to a different SCC. *)
    ultimately show ?thesis
      using all_v_in_SCC in_mono[OF E_closed_V] by fast
  qed
  (** This would mean that every SCC has a successor in the condensation. *)
  hence "\<forall>R\<in>SCCs. condensation `` {R} \<noteq> {}"
    unfolding SCCs_def
    using edge_in_condensation_iff by blast
  (** This makes the condensation a finite graph without dead ends. *)
  then interpret cond_V_succ: finite_graph_V_succ condensation SCCs
    by (unfold_locales) (auto simp: condensation_def)
  (** Since there exists an SCC, there now exists a cycle in the condensation.
      The condensation should not contain any cycles, so this is a contradiction. *)
  from SCC_ex[OF \<open>V\<noteq>{}\<close>] cond_V_succ.cycle_always_exists
  show False
    unfolding reachable_cycle_def SCCs_def
    using condensation_no_cycles by blast
qed
end (** End of context finite_graph_V *)


context finite_graph_V_succ
begin
(** In a graph where every node has a successor, every bottom SCC must be nontrivial. *)
lemma bottom_SCC_is_nontrivial:
  "bottom_SCC R \<longleftrightarrow> nt_bottom_SCC R"
proof
  (** R is a bottom SCC. *)
  assume bottom_SCC: "bottom_SCC R"
  (** There must exist at least one edge in R. *)
  moreover have "Restr E R \<noteq> {}"
  proof -
    {
      (** Every x in R is part of V. *)
      fix x assume "x \<in> R"
      with bottom_SCC have "x \<in> V"
        using bottom_SCC_in_V by blast
      (** Every node in V must have a successor, and R is closed because it is a
          bottom SCC, so every node in R must have a successor in R. *)
      from bottom_SCC \<open>x\<in>R\<close> have "\<exists>y. (x,y) \<in> E \<and> y \<in> R"
        unfolding bottom_SCC_def
        using succ[OF \<open>x\<in>V\<close>] by blast
    }
    (** Since R is not empty, this means the SCC contains at least one edge. *)
    moreover from bottom_SCC have "R \<noteq> {}" by auto
    ultimately show ?thesis by blast
  qed
  (** Therefore, this bottom SCC is nontrivial by its definition, proving one direction. *)
  ultimately show "nt_bottom_SCC R"
    by (simp add: nt_bottom_SCC_def)
(** Every nontrivial bottom SCC is always bottom by definition, proving the other direction. *)
qed (simp add: nt_bottom_SCC_def)

(** There always exists a nontrivial bottom SCC in a finite graph without dead ends. *)
lemma nt_bottom_SCC_ex:
  assumes "V \<noteq> {}"
  shows "\<exists>R. nt_bottom_SCC R"
  using bottom_SCC_ex[OF \<open>V\<noteq>{}\<close>] bottom_SCC_is_nontrivial
  by simp
end (** End of context finite_graph_V_succ *)

end
