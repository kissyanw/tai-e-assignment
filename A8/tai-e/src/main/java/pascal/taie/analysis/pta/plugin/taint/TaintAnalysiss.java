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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.lang.invoke.CallSite;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private final MultiMap<Pointer, Pointer> taintTransferEdges = Maps.newMultiMap();

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        CallGraph<CSCallSite, CSMethod> csCallGraph = result.getCSCallGraph();
        Stream<Edge<CSCallSite, CSMethod>> callEdges = csCallGraph.edges();
        callEdges.forEach(edge -> {
            CSCallSite csCallSite = edge.getCallSite();
            CSMethod csCallee = edge.getCallee();

            JMethod jMethod = csCallee.getMethod();
            if (isSink(jMethod)) {
                List<Integer> sinkParamIndexes = getSinkParamIndexes(jMethod);
                for (int index : sinkParamIndexes) {
                    CSVar sinkParam = csManager.getCSVar(csCallSite.getContext(), csCallSite.getCallSite().getInvokeExp().getArg(index));
                    Set<CSObj> pointedObjs = result.getPointsToSet(sinkParam);
                    for (CSObj csObj : pointedObjs) {
                        if (csObj.getObject() instanceof MockObj mockObj && mockObj.getDescription().equals("TaintObj")) {
                            Invoke sourceCall = (Invoke) mockObj.getAllocation();
                            Invoke sinkCall = csCallSite.getCallSite();
                            taintFlows.add(new TaintFlow(sourceCall, sinkCall, index));
                        }
                    }
                }
            }
        });

        return taintFlows;
    }

    public boolean isSource(JMethod jMethod, Type type) {
        for (Source source : config.getSources()) {
            if (source.method().equals(jMethod) && source.type().equals(type)) {
                return true;
            }
        }
        return false;
    }

    public boolean isSink(JMethod jMethod) {
        for (Sink sink : config.getSinks()) {
            if (sink.method().equals(jMethod)) {
                return true;
            }
        }
        return false;
    }

    public List<Integer> getSinkParamIndexes(JMethod jMethod) {
        List<Integer> indexes = new ArrayList<>();
        for (Sink sink : config.getSinks()) {
            if (sink.method().equals(jMethod)) {
                indexes.add(sink.index());
            }
        }
        return indexes;
    }

    public boolean isTaintTransferMethod(JMethod method) {
        for (TaintTransfer transfer : config.getTransfers()) {
            if (transfer.method().equals(method)) return true;
        }
        return false;
    }

    public CSObj makeTaintObj(Invoke source, Type type) {
        return csManager.getCSObj(emptyContext, manager.makeTaint(source, type));
    }


    public void addTaintTransferEdge(CSVar src, CSVar dest) {
        taintTransferEdges.put(src, dest);
    }

    public MultiMap<Pointer, Pointer> getTaintTransferEdges() {
        return taintTransferEdges;
    }

    public HashMap<Integer, Integer> getFromToIndexMap(JMethod callee) {
        HashMap<Integer, Integer> fromToIndexMap = new HashMap<>();
        for (TaintTransfer transfer : config.getTransfers()) {
            if (transfer.method().equals(callee)) {
                fromToIndexMap.put(transfer.from(), transfer.to());
            }
        }

        return fromToIndexMap;
    }

}
