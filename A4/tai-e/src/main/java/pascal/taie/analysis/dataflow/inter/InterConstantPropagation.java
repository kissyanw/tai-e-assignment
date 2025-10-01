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
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.*;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.Collection;
import java.util.List;
import java.util.Set;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact newOut = in.copy();
        return out.copyFrom(newOut);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        return cp.transferNode(stmt, in, out);
        // TODO - finish me
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        Stmt callSite = edge.getSource();

        CPFact callToReturnOut = out.copy();
        if (callSite instanceof Invoke invoke) {
            Var result = invoke.getResult();
            if (result != null && ConstantPropagation.canHoldInt(result)) {
                callToReturnOut.update(result, Value.getUndef());
            }
        }
        return callToReturnOut;

        // TODO - finish me
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        JMethod callee = edge.getCallee();
        List<Var> formal_params = callee.getIR().getParams();
        Invoke callSite = (Invoke) edge.getSource();
        List<Var> actual_params = callSite.getInvokeExp().getArgs();

        CPFact callEdgeOut = new CPFact();
        for(int i = 0; i < actual_params.size(); i++) {
            callEdgeOut.update(formal_params.get(i), callSiteOut.get(actual_params.get(i)));
        }

        // TODO - finish me
        return callEdgeOut;
    }

    //多个return的情况要怎么处理 简单的meetValue吗 可实在是获取不到returnStmt
    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact returnEdgeOut = returnOut.copy();
        for (Var var : returnOut.keySet()) {
            returnEdgeOut.update(var, Value.getUndef());
        }
        Stmt callSite = edge.getCallSite();
        if (callSite instanceof Invoke invoke) {
            Var result = invoke.getResult();
            if (result == null || !ConstantPropagation.canHoldInt(result)) {return null;}
            else {
                Value returnVal = Value.getUndef();
                Collection<Var> returnVars = edge.getReturnVars();
                for (Var returnVar : returnVars) {
                    returnVal = cp.meetValue(returnVal,returnOut.get(returnVar));
                }
                returnEdgeOut.update(result, returnVal);
            }
        }

        return returnEdgeOut;
    }
}
