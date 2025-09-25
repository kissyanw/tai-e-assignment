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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;
import polyglot.ast.While;

import java.util.*;

/**
controlflow reachable statements contains exit statement
 however, branch reachable statements may not contain exit statement
 */

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        Stmt entry = cfg.getEntry();

        //1. find the control-flow unreachable statements
        Set<Stmt> controlFlowReachableStmts = new HashSet<>();
        Queue<Stmt> queue = new LinkedList<>();
        queue.add(entry);
        controlFlowReachableStmts.add(entry);

        while(!queue.isEmpty()) {
            Stmt current = queue.poll();
            Set<Edge<Stmt>> outEdges = cfg.getOutEdgesOf(current);
            for (Edge<Stmt> edge: outEdges) {
                Stmt succ = edge.getTarget();
                if (!controlFlowReachableStmts.contains(succ)) {
                    controlFlowReachableStmts.add(succ);
                    queue.add(succ);
                }
            }
        }

        for (Stmt node : cfg.getNodes()) {
            if(cfg.isExit(node)) continue;
            if (!controlFlowReachableStmts.contains(node)) {
                deadCode.add(node);
            }
        }


        //2.find unreachable branch
        Set<Stmt> branchReachableStmts = new HashSet<>();
        queue = new LinkedList<>();
        queue.add(entry);
        branchReachableStmts.add(entry);

        while(!queue.isEmpty()) {
            Stmt current = queue.poll();
            Set<Edge<Stmt>> outEdges = cfg.getOutEdgesOf(current);

            if(current instanceof If ifStmt) {
                ConditionExp condition = ifStmt.getCondition();
                CPFact inFact = constants.getInFact(ifStmt);
                Value stmtValue = evaluate(condition, inFact);

                assert stmtValue != null;
                if (stmtValue.isConstant()) {
                    if (stmtValue.getConstant() != 0) {
                        for (Edge<Stmt> edge : outEdges) {
                            if (edge.getKind() == Edge.Kind.IF_TRUE) {
                                Stmt succ = edge.getTarget();
                                if (!branchReachableStmts.contains(succ)) {
                                    branchReachableStmts.add(succ);
                                    queue.add(succ);
                                }
                            }
                        }
                    }
                    else {
                        for (Edge<Stmt> edge : outEdges) {
                            if (edge.getKind() == Edge.Kind.IF_FALSE) {
                                Stmt succ = edge.getTarget();
                                if (!branchReachableStmts.contains(succ)) {
                                    branchReachableStmts.add(succ);
                                    queue.add(succ);
                                }
                            }
                        }
                    }
                }
                else {
                    for (Edge<Stmt> edge : outEdges) {
                        Stmt succ = edge.getTarget();
                        if (!branchReachableStmts.contains(succ)) {
                            branchReachableStmts.add(succ);
                            queue.add(succ);
                        }
                    }
                }

            }

            else if(current instanceof SwitchStmt switchStmt) {
                Var var = switchStmt.getVar();
                CPFact inFact = constants.getInFact(switchStmt);
                Value stmtValue = inFact.get(var);
                if (stmtValue.isConstant()) {
                    int constValue = stmtValue.getConstant();
                    List<Integer> caseValues =  switchStmt.getCaseValues();
                    if(caseValues.contains(constValue)) {
                        List<Pair<Integer,Stmt>> caseTargets = switchStmt.getCaseTargets();
                        for(Pair<Integer,Stmt> pair: caseTargets) {
                            if(pair.first() == constValue) {
                                Stmt succ = pair.second();
                                if (!branchReachableStmts.contains(succ)) {
                                    branchReachableStmts.add(succ);
                                    queue.add(succ);
                                }
                            }
                        }
                    }
                    else {
                        Stmt succ = switchStmt.getDefaultTarget();
                        if (!branchReachableStmts.contains(succ)) {
                            branchReachableStmts.add(succ);
                            queue.add(succ);
                        }
                    }
                }

                else {
                    for (Edge<Stmt> edge : outEdges) {
                        Stmt succ = edge.getTarget();
                        if (!branchReachableStmts.contains(succ)) {
                            branchReachableStmts.add(succ);
                            queue.add(succ);
                        }
                    }
                }
            }

            else {
                for (Edge<Stmt> edge : outEdges) {
                    Stmt succ = edge.getTarget();
                    if (!branchReachableStmts.contains(succ)) {
                        branchReachableStmts.add(succ);
                        queue.add(succ);
                    }
                }
            }
        }

        for (Stmt node : controlFlowReachableStmts) {
            if(cfg.isExit(node)) continue;
            if (!branchReachableStmts.contains(node)) {
                deadCode.add(node);
            }
        }

        //3. find the statements whose defined variables are not live afterwards
        for (Stmt node : branchReachableStmts) {
            if (node instanceof AssignStmt<?,?> assignStmt) {
                RValue rValue = assignStmt.getRValue();
                LValue lValue = assignStmt.getLValue();
                if (lValue instanceof Var definedVar && hasNoSideEffect(rValue)) {
                    SetFact<Var> outFact = liveVars.getOutFact(node);
                    if (!outFact.contains(definedVar)) deadCode.add(node);
                }
            }
        }

        return deadCode;
    }

    private static Value evaluate(Exp exp, CPFact inFact) {
        if (exp instanceof Var var) {
            return inFact.get(var);
        }
        else if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        else if (exp instanceof BinaryExp binaryExp) {
            Value v1 = inFact.get(binaryExp.getOperand1());
            Value v2 = inFact.get(binaryExp.getOperand2());
            if (v1.isNAC() || v2.isNAC()) {
                if (binaryExp instanceof ArithmeticExp) {
                    ArithmeticExp.Op op = (ArithmeticExp.Op) binaryExp.getOperator();
                    if (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM) {
                        // division by zero may happen
                        if (v2.isConstant() && v2.getConstant() == 0) {
                            return Value.getUndef();
                        }
                    }
                }
                return Value.getNAC();
            }
            else if (v1.isUndef() || v2.isUndef()) return Value.getUndef();
            else if (v1.isConstant() && v2.isConstant()) {
                if (binaryExp instanceof ArithmeticExp) {
                    return arithmeticEvaluate(binaryExp.getOperator(), v1, v2);
                }
                else if (binaryExp instanceof BitwiseExp) {
                    return bitwiseEvaluate(binaryExp.getOperator(), v1, v2);
                }
                else if (binaryExp instanceof ShiftExp) {
                    return shiftEvaluate(binaryExp.getOperator(), v1, v2);
                }
                else if (binaryExp instanceof ConditionExp) {
                    return conditionEvaluate(binaryExp.getOperator(), v1, v2);
                }
            }
        }

        return null;
    }

    private static Value conditionEvaluate(BinaryExp.Op operator, Value v1, Value v2) {
        int a = v1.getConstant();
        int b = v2.getConstant();
        return switch ((ConditionExp.Op) operator) {
            case EQ -> Value.makeConstant(a == b ? 1 : 0);
            case NE -> Value.makeConstant(a != b ? 1 : 0);
            case LT -> Value.makeConstant(a < b ? 1 : 0);
            case GT -> Value.makeConstant(a > b ? 1 : 0);
            case LE -> Value.makeConstant(a <= b ? 1 : 0);
            case GE -> Value.makeConstant(a >= b ? 1 : 0);
        };
    }

    private static Value shiftEvaluate(BinaryExp.Op operator, Value v1, Value v2) {
        int a = v1.getConstant();
        int b = v2.getConstant();
        return switch ((ShiftExp.Op) operator) {
            case SHL -> Value.makeConstant(a << b);
            case SHR -> Value.makeConstant(a >> b);
            case USHR -> Value.makeConstant(a >>> b);
        };
    }

    private static Value bitwiseEvaluate(BinaryExp.Op operator, Value v1, Value v2) {
        int a = v1.getConstant();
        int b = v2.getConstant();
        return switch ((BitwiseExp.Op) operator) {
            case AND -> Value.makeConstant(a & b);
            case OR -> Value.makeConstant(a | b);
            case XOR -> Value.makeConstant(a ^ b);
        };
    }

    private static Value arithmeticEvaluate(BinaryExp.Op operator, Value v1, Value v2) {
        int a = v1.getConstant();
        int b = v2.getConstant();
        return switch ((ArithmeticExp.Op) operator) {
            case ADD -> Value.makeConstant(a + b);
            case SUB -> Value.makeConstant(a - b);
            case MUL -> Value.makeConstant(a * b);
            case DIV -> {
                if (b == 0) yield Value.getUndef();
                else yield Value.makeConstant(a / b);
            }
            case REM -> {
                if (b == 0) yield Value.getUndef();
                else yield Value.makeConstant(a % b);
            }
        };
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
