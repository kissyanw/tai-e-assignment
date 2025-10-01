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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import polyglot.ast.Call;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);

        Queue<JMethod> worklist = new ArrayDeque<>();
        worklist.add(entry);

        while (!worklist.isEmpty()) {
            JMethod method = worklist.poll();
            if (callGraph.addReachableMethod(method)) {
                for(Invoke callSite : callGraph.getCallSitesIn(method)) {
                    CallKind callKind = CallGraphs.getCallKind(callSite);
                    Set<JMethod> callees = resolve(callSite);
                    for (JMethod callee: callees) {
                        Edge<Invoke, JMethod> edge = new Edge<>(callKind, callSite, callee);
                        callGraph.addEdge(edge);
                        worklist.add(callee);
                    }
                }
            }
        }

        // TODO - finish me
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> T = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        Subsignature subsignature = methodRef.getSubsignature();

        CallKind callKind = CallGraphs.getCallKind(callSite);
        if (callKind == CallKind.STATIC ) {
            JClass static_class = methodRef.getDeclaringClass();
            JMethod jMethod = static_class.getDeclaredMethod(subsignature);
            if (jMethod != null) T.add(jMethod);
        }
        else if( callKind == CallKind.SPECIAL){
            JClass m_class = methodRef.getDeclaringClass();
            JMethod jMethod = dispatch(m_class, subsignature);
            if (jMethod != null) T.add(jMethod);
        }
        else if (callKind == CallKind.VIRTUAL || callKind == CallKind.INTERFACE) {
            //这里是有问题的，遍历mtype的子集和遍历receiverobject type的子集并作dispatch的结果是不能保证一样的？
            JClass declared_receiver_class = methodRef.getDeclaringClass();
            Queue<JClass> subClasses = new ArrayDeque<>();
            //这个set主要是针对同级设计的
            Set<JClass> visited = new HashSet<>();
            subClasses.add(declared_receiver_class);

            while(!subClasses.isEmpty()) {
                JClass jClass = subClasses.poll();
                JMethod jMethod = dispatch(jClass, subsignature);
                if (jMethod != null) T.add(jMethod);

                //需要考虑接口和实现吗，这个算法的本质是？
                for (JClass sub : hierarchy.getDirectSubinterfacesOf(jClass)) {
                    if (visited.add(sub)) subClasses.add(sub);
                }
                for (JClass sub : hierarchy.getDirectImplementorsOf(jClass)) {
                    if (visited.add(sub)) subClasses.add(sub);
                }
                for (JClass sub : hierarchy.getDirectSubclassesOf(jClass)) {
                    if (visited.add(sub)) subClasses.add(sub);
                }
            }

        }
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JMethod jMethod = jclass.getDeclaredMethod(subsignature);
        if (jMethod != null && !jMethod.isAbstract()) {
            return jMethod;
        }
        else {
            JClass superClass = jclass.getSuperClass();
            if (superClass != null) {
                return dispatch(superClass, subsignature);
            }
        }
        return null;
    }
}
