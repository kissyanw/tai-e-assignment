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

import com.google.common.collect.Multimap;
import jas.CP;
import org.checkerframework.checker.units.qual.C;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.util.collection.MultiMap;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Maps;
import polyglot.visit.DataFlow;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.concurrent.Callable;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private final MultiMap<Var, Var> aliasVarMap = Maps.newMultiMap();

    private final MultiMap<LoadField, StoreField> aliasStaticFieldMap = Maps.newMultiMap();

    private final MultiMap<LoadField, StoreField> aliasInstanceFieldMap = Maps.newMultiMap();

    private final MultiMap<LoadArray, StoreArray> aliasArrayIndexMap = Maps.newMultiMap();


    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        Set<Stmt> stmts = icfg.getNodes();
        // build alias var map
        Collection<Var> vars = pta.getVars();
        for (Var var : vars) {
            Set<Obj> pts = pta.getPointsToSet(var);
            for (Var other : vars) {
                //应该和自身建立互为别名的关系
                Set<Obj> otherPts = pta.getPointsToSet(other);
                for (Obj obj : otherPts) {
                    if (pts.contains(obj)) {
                        aliasVarMap.put(var, other);
                        break;
                    }
                }
            }
        }

        // You can do initialization work here
        Set<LoadField> StaticLoadFieldStmts = stmts.stream()
                .filter(s -> s instanceof LoadField && ((LoadField) s).isStatic())
                .map(s -> (LoadField) s)
                .collect(java.util.stream.Collectors.toSet());

        Set<StoreField> StaticStoreFieldStmts = stmts.stream()
                .filter(s -> s instanceof StoreField && ((StoreField) s).isStatic())
                .map(s -> (StoreField) s)
                .collect(java.util.stream.Collectors.toSet());

        Set<LoadField> InstanceLoadFieldStmts = stmts.stream()
                .filter(s -> s instanceof LoadField && !((LoadField) s).isStatic())
                .map(s -> (LoadField) s)
                .collect(java.util.stream.Collectors.toSet());

        Set<StoreField> InstanceStoreFieldStmts = stmts.stream()
                .filter(s -> s instanceof StoreField && !((StoreField) s).isStatic())
                .map(s -> (StoreField) s)
                .collect(java.util.stream.Collectors.toSet());

        Set<LoadArray> LoadArrayStmts = stmts.stream()
                .filter(s -> s instanceof LoadArray)
                .map(s -> (LoadArray) s)
                .collect(java.util.stream.Collectors.toSet());

        Set<StoreArray> StoreArrayStmts = stmts.stream()
                .filter(s -> s instanceof StoreArray)
                .map(s -> (StoreArray) s)
                .collect(java.util.stream.Collectors.toSet());

        //build alias static field stmt map
        for (LoadField staticLoadFieldStmt : StaticLoadFieldStmts) {
            JField loadField = staticLoadFieldStmt.getFieldRef().resolve();
            for (StoreField staticStoreFieldStmt : StaticStoreFieldStmts) {
                JField storeField = staticStoreFieldStmt.getFieldRef().resolve();
                // JField在程序中是唯一的？
                if (loadField.equals(storeField)) {
                    aliasStaticFieldMap.put(staticLoadFieldStmt, staticStoreFieldStmt);
                }
            }
        }

        //build alias instance field stmt map
        for (LoadField instanceLoadFieldStmt : InstanceLoadFieldStmts) {
            JField loadField = instanceLoadFieldStmt.getFieldRef().resolve();
            InstanceFieldAccess loadFieldAccess = (InstanceFieldAccess) instanceLoadFieldStmt.getFieldAccess();
            Var loadBase = loadFieldAccess.getBase();

            for (StoreField instanceStoreFieldStmt : InstanceStoreFieldStmts) {
                JField storeField = instanceStoreFieldStmt.getFieldRef().resolve();
                Var storeBase = ((InstanceFieldAccess) instanceStoreFieldStmt.getFieldAccess()).getBase();
                // JField在程序中是唯一的？
                if (aliasVarMap.get(loadBase).contains(storeBase) && loadField.equals(storeField)) {
                    aliasInstanceFieldMap.put(instanceLoadFieldStmt, instanceStoreFieldStmt);
                }
            }
        }

        //build alias array index stmt map
        for (LoadArray loadArrayStmt : LoadArrayStmts) {
            Var loadBase = loadArrayStmt.getArrayAccess().getBase();
            for (StoreArray storeArrayStmt : StoreArrayStmts) {
                Var storeBase = storeArrayStmt.getArrayAccess().getBase();
                if (aliasVarMap.get(loadBase).contains(storeBase)) {
                    aliasArrayIndexMap.put(loadArrayStmt, storeArrayStmt);
                }
            }
            int x = 1;
        }

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
        // nothing happens here 恒等意味着out与本轮的In相同 但是不意味着out与上一轮out相同
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        boolean changed = cp.transferNode(stmt, in, out);

        //alias-aware transfer
        if (stmt instanceof LoadField loadField) {
            if (loadField.isStatic()) {
                Var loadVar = loadField.getLValue();
                Value initialValue = in.get(loadVar);
                Value newValue = Value.getUndef();
                Collection<StoreField> aliasStoreFieldStmts = aliasStaticFieldMap.get(loadField);
                if (aliasStoreFieldStmts.isEmpty()) return changed;
                else {
                    for (StoreField aliasStoreFieldStmt : aliasStoreFieldStmts) {
                        Var storeVar = aliasStoreFieldStmt.getRValue();
                        Value storeValue = in.get(storeVar);
                        newValue = cp.meetValue(storeValue, newValue);
                    }
                    if (!newValue.equals(initialValue)) changed = true;
                    out.update(loadVar, newValue);
                }

            }
            else {
                Var loadVar = loadField.getLValue();
                Value initialValue = in.get(loadVar);
                Value newValue = Value.getUndef();
                Collection<StoreField> aliasStoreFieldStmts = aliasInstanceFieldMap.get(loadField);
                if (aliasStoreFieldStmts.isEmpty()) return changed;
                else {
                    for (StoreField aliasStoreFieldStmt : aliasStoreFieldStmts) {
                        Var storeVar = aliasStoreFieldStmt.getRValue();
                        Value storeValue = in.get(storeVar);
                        newValue = cp.meetValue(storeValue, initialValue);
                    }
                    if (!newValue.equals(initialValue)) changed = true;
                    out.update(loadVar, newValue);
                }
            }
            return changed;
        }
        else if (stmt instanceof LoadArray loadArray) {
            Var loadVar = loadArray.getLValue();
            Value initialValue = in.get(loadVar);
            Value newValue = Value.getUndef();
            Collection<StoreArray> aliasStoreArrayStmts = aliasArrayIndexMap.get(loadArray);
            Collection<StoreArray> aliasStoreArrayStmtsFiltered = new java.util.HashSet<>();
            //refine alias arrayIndexMap
            Var index = loadArray.getArrayAccess().getIndex();
            Value indexValue = in.get(index);
            if (indexValue.isUndef()) return changed;
            else if (indexValue.isConstant()) {
                for (StoreArray aliasStoreArrayStmt : aliasStoreArrayStmts) {
                    Var storeIndex = aliasStoreArrayStmt.getArrayAccess().getIndex();
                    //判断storeIndex的值 应该参考storestmt的上下文 而不是loadstmt的上下文
                    //todo
                    CPFact storeFact = solver.getInFact(aliasStoreArrayStmt);
                    Value storeIndexValue = storeFact.get(storeIndex);
                    if (storeIndexValue.isUndef()) continue;
                    else if (storeIndexValue.isConstant() && storeIndexValue.equals(indexValue)) {
                        aliasStoreArrayStmtsFiltered.add(aliasStoreArrayStmt);
                    }
                    else if (storeIndexValue.isNAC()) {
                        aliasStoreArrayStmtsFiltered.add(aliasStoreArrayStmt);
                    }
                }
            }
            else if (indexValue.isNAC()) {
                for (StoreArray aliasStoreArrayStmt : aliasStoreArrayStmts ) {
                    Var storeIndex = aliasStoreArrayStmt.getArrayAccess().getIndex();
                    Value storeIndexValue = in.get(storeIndex);
                    if (storeIndexValue.isUndef()) continue;
                    else aliasStoreArrayStmtsFiltered.add(aliasStoreArrayStmt);
                }
            }

            if (aliasStoreArrayStmtsFiltered.isEmpty()) return changed;
            else {
                for (StoreArray aliasStoreArrayStmt : aliasStoreArrayStmtsFiltered) {
                    Var storeVar = aliasStoreArrayStmt.getRValue();
                    Value storeValue = in.get(storeVar);
                    newValue = cp.meetValue(storeValue, initialValue);
                }
                if (!newValue.equals(initialValue)) changed = true;
                out.update(loadVar, newValue);
            }
            return changed;
        }
        else return changed;
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        //nothing happens here
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        Stmt callSite = edge.getSource();
        CPFact fact = out.copy();
        if (callSite instanceof Invoke invoke) {
            Var result = invoke.getResult();
            if (result != null) fact.remove(result);
        }

        return fact;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        Stmt callSite = edge.getSource();
        CPFact fact = new CPFact();
        //初始化calledgeout 不能copy callsiteout 因为根据实参删除会删不干净上下文信息
        JMethod callee = edge.getCallee();

        if (callSite instanceof Invoke invoke) {
            List<Var> actual_params = invoke.getInvokeExp().getArgs();
            List<Var> formal_params = callee.getIR().getParams();
            for (int i = 0; i < actual_params.size(); i++) {
                Var actual_param = actual_params.get(i);
                Var formal_param = formal_params.get(i);
                fact.update(formal_param, callSiteOut.get(actual_param));
            }
        }

        return fact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        Stmt callSite = edge.getCallSite();
        //returnedgeout 也要初始化为空 防止带上callee上下文信息
        CPFact fact = new CPFact();
        if (callSite instanceof Invoke invoke) {
            Var result = invoke.getResult();
            Collection<Var> returnVars = edge.getReturnVars();
            Value retValue = Value.getUndef();
            if ( result != null) {
                for (Var var : returnVars) {
                    Value value = returnOut.get(var);
                    retValue = cp.meetValue(value, retValue);
                }
                fact.update(result, retValue);
            }

        }

        return fact;
    }

}
