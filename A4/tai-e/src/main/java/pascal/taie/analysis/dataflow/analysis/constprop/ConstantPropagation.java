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

package pascal.taie.analysis.dataflow.analysis.constprop;

import fj.P;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.Optional;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact fact = new CPFact();
        for (Var var : cfg.getIR().getVars()) {
            if (canHoldInt(var)) fact.update(var, Value.getUndef());
        }

        for (Var var : cfg.getIR().getParams()) {
            if (canHoldInt(var)) fact.update(var, Value.getNAC());
        }

        if (cfg.getIR().getThis() != null && canHoldInt(cfg.getIR().getThis())) fact.update(cfg.getIR().getThis(), Value.getNAC());
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var var : fact.keySet()) {
            Value v1 = fact.get(var);
            Value v2 = target.get(var);
            Value meetV = meetValue(v1, v2);
            target.update(var, meetV);
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
        else if (v1.isUndef() && v2.isConstant()) return v2;
        else if (v1.isConstant() && v2.isUndef()) return v1;
        else if (v1.isUndef() && v2.isUndef()) return Value.getUndef();
        else if (v1.isConstant() && v2.isConstant() && v1.equals(v2)) return v1;
        else return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof DefinitionStmt<?,?> definitionStmt) {
            LValue left = definitionStmt.getLValue();
            RValue right = definitionStmt.getRValue();

            CPFact newOut = in.copy();

            if (left instanceof Var var) {
                if (canHoldInt(var)) {
                    Value value = evaluate(right, in);
                    newOut.update(var, value);
                }
                return out.copyFrom(newOut);
            }
        }
        return false;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof Var var) {
            return in.get(var);
        }
        else if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        else if (exp instanceof BinaryExp binaryExp) {
            Var var1 = binaryExp.getOperand1();
            Var var2 = binaryExp.getOperand2();
            Value v1 = in.get(var1);
            Value v2 = in.get(var2);
            if (v1.isUndef() || v2.isUndef()) return Value.getUndef();
            else if (v1.isNAC() || v2.isNAC()) {
                if (binaryExp instanceof ArithmeticExp arithmeticExp) {
                    if (arithmeticExp.getOperator() == ArithmeticExp.Op.DIV || arithmeticExp.getOperator() == ArithmeticExp.Op.REM) {
                        if (v2.isConstant() && v2.getConstant() == 0) return Value.getUndef();
                    }
                }
                return Value.getNAC();
            }
            else {
                if (binaryExp instanceof ArithmeticExp arithmeticExp) {
                    return arithmeticEvaluate(arithmeticExp.getOperator(), v1, v2);
                }
                else if (binaryExp instanceof BitwiseExp bitwiseExp) {
                    return bitwiseEvaluate(bitwiseExp.getOperator(), v1, v2);
                }
                else if (binaryExp instanceof ConditionExp conditionExp) {
                    return conditionEvaluate(conditionExp.getOperator(), v1, v2);
                }
                else if (binaryExp instanceof ShiftExp shiftExp) {
                    return shiftEvaluate(shiftExp.getOperator(), v1, v2);
                }
                else {
                    throw new AnalysisException("Unknown binary expression: " + binaryExp);
                }
            }

        }
        else return Value.getNAC();
    }

    private static Value arithmeticEvaluate(ArithmeticExp.Op operator, Value v1, Value v2) {
        int val1 = v1.getConstant();
        int val2 = v2.getConstant();
        return switch (operator) {
            case ADD -> Value.makeConstant(val1 + val2);
            case SUB -> Value.makeConstant(val1 - val2);
            case MUL -> Value.makeConstant(val1 * val2);
            case DIV -> {
                if (val2 == 0) yield Value.getUndef();
                yield Value.makeConstant(val1 / val2);
            }
            case REM -> {
                if (val2 == 0) yield Value.getUndef();
                yield Value.makeConstant(val1 % val2);
            }
            default -> throw new AnalysisException("Unknown arithmetic operator: " + operator);
        };
    }

    private static Value bitwiseEvaluate(BitwiseExp.Op operator, Value v1, Value v2) {
        int val1 = v1.getConstant();
        int val2 = v2.getConstant();
        return switch (operator) {
            case AND -> Value.makeConstant(val1 & val2);
            case OR -> Value.makeConstant(val1 | val2);
            case XOR -> Value.makeConstant(val1 ^ val2);
            default -> throw new AnalysisException("Unknown bitwise operator: " + operator);
        };
    }

    private static Value conditionEvaluate(ConditionExp.Op operator, Value v1, Value v2) {
        int val1 = v1.getConstant();
        int val2 = v2.getConstant();
        return switch (operator) {
            case EQ -> Value.makeConstant(val1 == val2 ? 1 : 0);
            case NE -> Value.makeConstant(val1 != val2 ? 1 : 0);
            case LT -> Value.makeConstant(val1 < val2 ? 1 : 0);
            case GT -> Value.makeConstant(val1 > val2 ? 1 : 0);
            case LE -> Value.makeConstant(val1 <= val2 ? 1 : 0);
            case GE -> Value.makeConstant(val1 >= val2 ? 1 : 0);
            default -> throw new AnalysisException("Unknown condition operator: " + operator);
        };
    }

    private static Value shiftEvaluate(ShiftExp.Op operator, Value v1, Value v2) {
        int val1 = v1.getConstant();
        int val2 = v2.getConstant();
        return switch (operator) {
            case SHL -> Value.makeConstant(val1 << val2);
            case SHR -> Value.makeConstant(val1 >> val2);
            case USHR -> Value.makeConstant(val1 >>> val2);
            default -> throw new AnalysisException("Unknown shift operator: " + operator);
        };
    }
}
