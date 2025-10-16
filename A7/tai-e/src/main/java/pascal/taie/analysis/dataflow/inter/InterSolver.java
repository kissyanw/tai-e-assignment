/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.util.collection.SetQueue;

import java.util.ArrayDeque;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        icfg.getNodes().forEach(node -> {
            result.setInFact(node, analysis.newInitialFact());
            result.setOutFact(node, analysis.newInitialFact());
        });

        icfg.entryMethods().forEach(entryMethod -> {
            Node entryNode = icfg.getEntryOf(entryMethod);
            result.setInFact(entryNode, analysis.newBoundaryFact(entryNode));
            result.setOutFact(entryNode, analysis.newBoundaryFact(entryNode));
        });
        // TODO - finish me
    }

    private void doSolve() {
        // TODO - finish me
        workList = new ArrayDeque<>();
        workList.addAll(icfg.getNodes());

        while (!workList.isEmpty()) {
            Node node = workList.poll();
            Fact in = analysis.newInitialFact();
            for (ICFGEdge<Node> inEdge : icfg.getInEdgesOf(node)) {
                Node pred = inEdge.getSource();
                Fact predOut = result.getOutFact(pred);
                Fact edgeOut = analysis.transferEdge(inEdge, predOut);
                analysis.meetInto(edgeOut, in);
            }
            //问题出在worklist遍历到Load语句的时候 部分store语句的上下文还没有更新 因此不只是get对应的result
            //处理store语句时 把相关联的load语句添加到worklist中 保证load语句的结果考虑到了最新的store更新
            result.setInFact(node, in);
            if (analysis.transferNode(node, in, result.getOutFact(node))) {
                workList.addAll(icfg.getSuccsOf(node));
            }
        }
    }

    public Fact getInFact(Node node) {
        return result.getInFact(node);
    }

    public void add(Node node) {
        workList.add(node);
    }

}
