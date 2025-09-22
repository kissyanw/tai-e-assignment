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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        List<Node> workList = new LinkedList<>(cfg.getNodes());
        while (!workList.isEmpty()) {
            Node node = workList.remove(0);
            Fact out = result.getOutFact(node);
            Fact in = analysis.newInitialFact();
            for (Node pred : cfg.getPredsOf(node)) {
                Fact pred_out = result.getOutFact(pred);
                //取并是不包括上一次迭代的in值的
                analysis.meetInto(pred_out,in);
            }
            result.setInFact(node, in);
            if (analysis.transferNode(node, in, out)) {
                workList.addAll(cfg.getSuccsOf(node));
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        List<Node> workList = new LinkedList<>(cfg.getNodes());
        while (!workList.isEmpty()) {
            Node node = workList.remove(0);
            Fact in = result.getInFact(node);
            Fact out = analysis.newInitialFact();
            for (Node succ : cfg.getSuccsOf(node)) {
                Fact fact = result.getInFact(succ);
                //取并是不包括上一次迭代的in值的
                analysis.meetInto(fact, out);
            }
            result.setOutFact(node, out);
            if(analysis.transferNode(node, in, out)) {
                workList.addAll(cfg.getPredsOf(node));
            };

        }
    }
}
