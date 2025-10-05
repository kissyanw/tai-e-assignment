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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        // contains refer to reachableMethods Set and have nothing to do with entryMethods Set
        if (callGraph.addReachableMethod(method)) {
            method.getIR().forEach(stmt -> {
                stmt.accept(stmtProcessor);
            });
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            Var var = stmt.getLValue();
            VarPtr varPtr = pointerFlowGraph.getVarPtr(var);
            Obj obj = heapModel.getObj(stmt);

            PointsToSet pointsToSet = new PointsToSet(obj);
            workList.addEntry(varPtr, pointsToSet);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var srcVar = stmt.getRValue();
            Var trgVar = stmt.getLValue();
            VarPtr srcPtr = pointerFlowGraph.getVarPtr(srcVar);
            VarPtr trgPtr = pointerFlowGraph.getVarPtr(trgVar);

            addPFGEdge(srcPtr, trgPtr);
            return null;
        }

        public Void visit(LoadField stmt) {
            Var trgVar = stmt.getLValue();
            VarPtr trgPtr = pointerFlowGraph.getVarPtr(trgVar);

            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                StaticField staticField = pointerFlowGraph.getStaticField(field);
                addPFGEdge(staticField, trgPtr);
            }

            return null;
        }

        public Void visit(StoreField stmt) {
            Var srcVar = stmt.getRValue();
            VarPtr srcPtr = pointerFlowGraph.getVarPtr(srcVar);

            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                StaticField staticField = pointerFlowGraph.getStaticField(field);
                addPFGEdge(srcPtr, staticField);
            }
            return null;
        }

        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod callee = resolveCallee(null, stmt);

                if (callee != null) {
                    if(callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, callee))) {
                        addReachable(callee);
                        List<Var> actual_params = stmt.getInvokeExp().getArgs();
                        List<Var> formal_params = callee.getIR().getParams();
                        List<Var> return_vars = callee.getIR().getReturnVars();

                        for (int i = 0; i < actual_params.size(); i++) {
                            VarPtr actualPtr = pointerFlowGraph.getVarPtr(actual_params.get(i));
                            VarPtr formalPtr = pointerFlowGraph.getVarPtr(formal_params.get(i));
                            addPFGEdge(actualPtr, formalPtr);
                        }

                        if (stmt.getResult() != null)  {
                            VarPtr resultPtr = pointerFlowGraph.getVarPtr(stmt.getResult());
                            for (Var returnVar : return_vars) {
                                VarPtr returnPtr = pointerFlowGraph.getVarPtr(returnVar);
                                addPFGEdge(returnPtr, resultPtr);
                            }
                        }
                    }
                }

            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet sourcePts = source.getPointsToSet();
            if (!sourcePts.isEmpty()) {
                workList.addEntry(target, sourcePts);
            }
        }
        // TODO - finish me
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pointsToSet = entry.pointsToSet();
            PointsToSet diff = propagate(pointer, pointsToSet);
            if (!diff.isEmpty() && pointer instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                for (Obj obj : diff.getObjects()) {
                    for (LoadField loadField : var.getLoadFields()) {
                        Var lValue = loadField.getLValue();
                        VarPtr trgPtr = pointerFlowGraph.getVarPtr(lValue);
                        InstanceField srcPtr = pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve());
                        addPFGEdge(srcPtr, trgPtr);
                    }
                    for (StoreField storeField : var.getStoreFields()) {
                        VarPtr srcPtr = pointerFlowGraph.getVarPtr(storeField.getRValue());
                        InstanceField trgPtr = pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve());
                        addPFGEdge(srcPtr, trgPtr);
                    }
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        VarPtr trgPtr = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        ArrayIndex srcPtr = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(srcPtr, trgPtr);
                    }
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        VarPtr srcPtr = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        ArrayIndex trgPtr = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(srcPtr, trgPtr);
                    }
                    processCall(var, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet pts = pointer.getPointsToSet();
        PointsToSet diff = new PointsToSet();
        for (Obj obj : pointsToSet.getObjects()) {
            if (pts.addObject(obj)) diff.addObject(obj);
        }
        if (!diff.isEmpty()) {
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, diff);
            }
        }
        return diff;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke callSite : var.getInvokes()) {
            JMethod callee = resolveCallee(recv, callSite);
            if (callee != null) {
                CallKind callKind = CallKind.OTHER;
                if (callSite.isSpecial()) callKind = CallKind.SPECIAL;
                else if (callSite.isInterface()) callKind = CallKind.INTERFACE;
                else if (callSite.isVirtual()) callKind = CallKind.VIRTUAL;
                else if (callSite.isStatic()) callKind = CallKind.STATIC;

                if (callKind != CallKind.STATIC) {
                    VarPtr thisPtr = pointerFlowGraph.getVarPtr(callee.getIR().getThis());
                    workList.addEntry(thisPtr, new PointsToSet(recv));
                }

                if (callGraph.addEdge(new Edge<>(callKind, callSite, callee))) {
                    addReachable(callee);
                    List<Var> actual_params = callSite.getInvokeExp().getArgs();
                    List<Var> formal_params = callee.getIR().getParams();
                    List<Var> return_vars = callee.getIR().getReturnVars();

                    for (int i = 0; i < actual_params.size(); i++) {
                        VarPtr actualPtr = pointerFlowGraph.getVarPtr(actual_params.get(i));
                        VarPtr formalPtr = pointerFlowGraph.getVarPtr(formal_params.get(i));
                        addPFGEdge(actualPtr, formalPtr);
                    }

                    if (callSite.getResult() != null)  {
                        VarPtr resultPtr = pointerFlowGraph.getVarPtr(callSite.getResult());
                        for (Var returnVar : return_vars) {
                            VarPtr returnPtr = pointerFlowGraph.getVarPtr(returnVar);
                            addPFGEdge(returnPtr, resultPtr);
                        }
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
