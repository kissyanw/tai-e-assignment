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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     * build static PFG edges according to its statements
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (callGraph.addReachableMethod(csMethod)) {
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            // pass the class type info of stmt to visit methods through implemention visit method in each Stmt class
            for (Stmt stmt : csMethod.getMethod().getIR()) stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            //no effect to taint analysis
            Obj obj = heapModel.getObj(stmt);
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            CSObj csObj = csManager.getCSObj(heapContext, obj);
            CSVar csVar = csManager.getCSVar(context, stmt.getLValue());
            workList.addEntry(csVar, PointsToSetFactory.make(csObj));

            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            // no need to propagate taint info specifically here, as it will be handled in the general pointer analysis propagation
            CSVar srcVar = csManager.getCSVar(context, stmt.getRValue());
            CSVar destVar = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(srcVar, destVar);

            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                JField jField = stmt.getFieldRef().resolve();
                //source: static field
                StaticField staticField = csManager.getStaticField(jField);
                CSVar destVar = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(staticField, destVar);
            }

            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                JField jField = stmt.getFieldRef().resolve();
                CSVar srcVar = csManager.getCSVar(context, stmt.getRValue());
                //target: static field
                StaticField staticField = csManager.getStaticField(jField);
                addPFGEdge(srcVar, staticField);
            }

            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod callee = resolveCallee(null, stmt);
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Context calleeContext = contextSelector.selectContext(csCallSite, callee);
                CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
                Type returnType = callee.getReturnType();

                //theoretically, the action to add c:l -> ct:m for static method will be taken only once during the analysis
                //so maybe no need to check the return value of addEdge here and it will always be true
                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite, csCallee))) {
                    //c1:l1 -> ct:m
                    //c2:l2 -> ct:m
                    //no need to add ct:m for twice?
                    //of course, and i can lay this part logic into addReachable method
//                    if (callGraph.addReachableMethod(csCallee)){
                    addReachable(csCallee);
//                    }
                    AddEdgeBetweenCallSiteAndCallee(csCallSite, csCallee);
                    //the static method call can be source of taint data flow
                    if (taintAnalysis.isSource(callee, returnType)) {
                        CSObj taintData  = taintAnalysis.makeTaintObj(stmt, returnType);
                        CSVar destVar = csManager.getCSVar(context, stmt.getResult());
                        workList.addEntry(destVar, PointsToSetFactory.make(taintData));
                    }
                    //no need to consider taint transfer when deal with static method;
                    //when the taint data is propagated to
                    //todo: if i should build virtual edge(only for propagating taint data) from arg to result for taintTransfer static method?
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet pointsToSet = source.getPointsToSet();
            if (!pointsToSet.isEmpty()) {
                workList.addEntry(target, pointsToSet);
            }
        }
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
            PointsToSet diffSet = propagate(pointer, pointsToSet);

            if (!diffSet.isEmpty() && pointer instanceof CSVar csVar) {
                Var var = csVar.getVar();
                Context context = csVar.getContext();
                List<LoadField> loadFields = var.getLoadFields();
                List<StoreField> storeFields = var.getStoreFields();
                List<StoreArray> storeArrays = var.getStoreArrays();
                List<LoadArray> loadArrays = var.getLoadArrays();

                for (CSObj csObj : diffSet) {
                    for (LoadField loadField : loadFields) {
                        CSVar dest = csManager.getCSVar(context, loadField.getLValue());
                        JField jField = loadField.getFieldRef().resolve();
                        InstanceField src = csManager.getInstanceField(csObj, jField);
                        addPFGEdge(src, dest);
                    }
                    for (StoreField storeField: storeFields) {
                        CSVar src = csManager.getCSVar(context, storeField.getRValue());
                        JField jField = storeField.getFieldRef().resolve();
                        InstanceField dest = csManager.getInstanceField(csObj, jField);
                        addPFGEdge(src, dest);
                    }
                    for (LoadArray loadArray: loadArrays) {
                        CSVar dest = csManager.getCSVar(context, loadArray.getLValue());
                        ArrayIndex src = csManager.getArrayIndex(csObj);
                        addPFGEdge(src, dest);
                    }
                    for (StoreArray storeArray: storeArrays) {
                        CSVar src = csManager.getCSVar(context, storeArray.getRValue());
                        ArrayIndex dest = csManager.getArrayIndex(csObj);
                        addPFGEdge(src, dest);
                    }
                    processCall(csVar, csObj);
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
        PointsToSet diffSet = PointsToSetFactory.make();

        for (CSObj csObj : pointsToSet) {
            if (!pts.contains(csObj)) {
                pts.addObject(csObj);
                diffSet.addObject(csObj);
            }
        }

        if (!diffSet.isEmpty()) {
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, diffSet);
            }
        }
        return diffSet;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        Var var = recv.getVar();
        Context context = recv.getContext();
        List<Invoke> invokes = var.getInvokes();

        for (Invoke callSite : invokes) {
            JMethod callee = resolveCallee(recvObj, callSite);
            CSCallSite csCallSite = csManager.getCSCallSite(context, callSite);
            Context calleeContext = contextSelector.selectContext(csCallSite, recvObj, callee);
            CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);

            CallKind callKind = CallKind.OTHER;
            if (callSite.isInterface()) callKind = CallKind.INTERFACE;
            else if (callSite.isVirtual()) callKind = CallKind.VIRTUAL;
            else if (callSite.isSpecial()) callKind = CallKind.SPECIAL;

            if (callGraph.addEdge(new Edge<>(callKind, csCallSite, csCallee))) {
                addReachable(csCallee);
                CSVar calleeThis = csManager.getCSVar(calleeContext, callee.getIR().getThis());
                workList.addEntry(calleeThis, PointsToSetFactory.make(recvObj));

                AddEdgeBetweenCallSiteAndCallee(csCallSite, csCallee);
            }

        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }

    private void AddEdgeBetweenCallSiteAndCallee(CSCallSite csCallSite, CSMethod csCallee) {
        List<Var> arguments = csCallSite.getCallSite().getInvokeExp().getArgs();
        List<Var> parameters = csCallee.getMethod().getIR().getParams();
        Context calleeContext = csCallee.getContext();
        Context callSiteContext = csCallSite.getContext();
        for (int i = 0; i < arguments.size(); i++) {
            CSVar srcVar = csManager.getCSVar(callSiteContext, arguments.get(i));
            CSVar destVar = csManager.getCSVar(calleeContext, parameters.get(i));
            addPFGEdge(srcVar, destVar);
        }

        if (csCallSite.getCallSite().getResult() != null) {
            List<Var> retVars = csCallee.getMethod().getIR().getVars();
            CSVar destVar = csManager.getCSVar(callSiteContext, csCallSite.getCallSite().getResult());
            for (Var retVar : retVars) {
                CSVar srcVar = csManager.getCSVar(calleeContext, retVar);
                addPFGEdge(srcVar, destVar);
            }
        }
    }
}
