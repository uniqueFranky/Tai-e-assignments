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
import pascal.taie.ir.IR;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.ConcurrentLinkedQueue;

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
        // TODO - finish me
        Queue<JMethod> q = new ConcurrentLinkedQueue<>();
        q.add(entry);

        while(!q.isEmpty()) {
            JMethod jMethod = q.remove();
            if(!callGraph.reachableMethods.contains(jMethod)) {
                callGraph.addReachableMethod(jMethod);
                IR ir = jMethod.getIR();
                for(Stmt stmt: ir) {
                    if(stmt instanceof Invoke invoke) {
                        Set<JMethod> callees = resolve(invoke);
                        for(JMethod callee: callees) {
                            callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, callee));
                        }
                        q.addAll(callees);
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> result = new HashSet<>();
        JClass jClass = callSite.getMethodRef().getDeclaringClass();
        Subsignature subsignature = callSite.getMethodRef().getSubsignature();
        CallKind callKind = CallGraphs.getCallKind(callSite);
        if(CallKind.STATIC == callKind || CallKind.SPECIAL == callKind) {
            JMethod res = dispatch(jClass, subsignature);
            if(null != res) {
                result.add(res);
            }
        } else {
            Queue<JClass> q = new ConcurrentLinkedQueue<>();
            q.add(jClass);
            while(!q.isEmpty()) {
                JClass klass = q.remove();
                JMethod res = dispatch(klass, subsignature);
                if(null != res) {
                    result.add(res);
                }
                q.addAll(hierarchy.getDirectSubclassesOf(klass));
                q.addAll(hierarchy.getDirectImplementorsOf(klass));
                q.addAll(hierarchy.getDirectSubinterfacesOf(klass));
            }
        }
        return result;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if(null == jclass) {
            return null;
        }
        JMethod declaredMethod = jclass.getDeclaredMethod(subsignature);
        if(null != declaredMethod && !declaredMethod.isAbstract()) {
            return declaredMethod;
        } else {
            return dispatch(jclass.getSuperClass(), subsignature);
        }
    }
}
