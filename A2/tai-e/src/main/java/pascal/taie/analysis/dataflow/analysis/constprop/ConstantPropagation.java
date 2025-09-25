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

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static pascal.taie.ir.exp.ArithmeticExp.Op.*;

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
    //extract all the var from cfg and add them to boundary fact with value as udf(bot)
    //set params and this as NAC
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact boundary = new CPFact();

        for (Var var : cfg.getIR().getVars()) {
            if (canHoldInt(var)) boundary.update(var, Value.getUndef());
        }

        for(Var var : cfg.getIR().getParams()) {
            if (canHoldInt(var)) boundary.update(var, Value.getNAC());
        }

        if (cfg.getIR().getThis() != null && canHoldInt(cfg.getIR().getThis())) {
            boundary.update(cfg.getIR().getThis(), Value.getNAC());
        }
        return boundary;
        // TODO - finish me
    }

    @Override
    // create a top fact which is used to initialize the dataflow analysis result for each node except entry node
    // in and out for each node is initialized as undefined(bot)
    public CPFact newInitialFact() {

        return new CPFact();
        // TODO - finish me
    }

    @Override
    //bring fact into target
    public void meetInto(CPFact fact, CPFact target) {
        for (Var var : fact.keySet()) {
            Value source = fact.get(var);
            target.update(var,meetValue(source,target.get(var)));
        }
        // TODO - finish me
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
        else if (v1.isUndef() && v2.isConstant()) return v2;
        else if (v1.isConstant() && v2.isUndef()) return v1;
        else if (v1.isUndef() && v2.isUndef()) return Value.getUndef();
        else if (v1.isConstant() && v2.isConstant()) {
            if (v1.equals(v2)) return v1;
            else return Value.getNAC();
        }
        // TODO - finish me
        return null;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact newOut = in.copy();
        if (stmt instanceof DefinitionStmt defStmt) {
            LValue left = defStmt.getLValue();
            RValue right = defStmt.getRValue();

            if (left instanceof Var leftVar) {
                if (canHoldInt(leftVar)) {
                    Value rightValue = evaluate(right, in);
                    if (rightValue != null) newOut.update(leftVar, rightValue);
                }
            }
        }

        return out.copyFrom(newOut);
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
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        else if (exp instanceof Var) {
            return in.get((Var) exp);
        }
        else if (exp instanceof BinaryExp binExp) {
            Value v1 = in.get(binExp.getOperand1());
            Value v2 = in.get(binExp.getOperand2());
            if (v1.isNAC() || v2.isNAC()) {
                if (binExp instanceof ArithmeticExp) {
                    ArithmeticExp.Op op = (ArithmeticExp.Op) binExp.getOperator();
                    if (op == DIV || op == REM) {
                        // division by zero may happen
                        if (v2.isConstant() && v2.getConstant() == 0) {
                            return Value.getUndef();
                        }
                    }
                }
                return Value.getNAC();
            }
            else if (v1.isUndef() || v2.isUndef()) return Value.getUndef();
            else {
                if (binExp instanceof ArithmeticExp) {
                    return arithmeticEvaluate(binExp.getOperator(), v1, v2);
                }
                else if (binExp instanceof BitwiseExp) {
                    return bitwiseEvaluate(binExp.getOperator(), v1, v2);
                }
                else if (binExp instanceof ShiftExp) {
                    return shiftEvaluate(binExp.getOperator(), v1, v2);
                }
                else if (binExp instanceof ConditionExp) {
                    return conditionEvaluate(binExp.getOperator(), v1, v2);
                }
            }
        }
        else {
            return Value.getNAC();
        }
        // TODO - finish me
        return null;
    }

    private static Value conditionEvaluate(BinaryExp.Op operator, Value v1, Value v2) {
        ConditionExp.Op op = (ConditionExp.Op) operator;
        int a = v1.getConstant();
        int b = v2.getConstant();
        return switch (op) {
            case EQ -> Value.makeConstant(a == b ? 1 : 0);
            case NE -> Value.makeConstant(a != b ? 1 : 0);
            case LT -> Value.makeConstant(a < b ? 1 : 0);
            case GT -> Value.makeConstant(a > b ? 1 : 0);
            case LE -> Value.makeConstant(a <= b ? 1 : 0);
            case GE -> Value.makeConstant(a >= b ? 1 : 0);
        };

    }

    private static Value shiftEvaluate(BinaryExp.Op operator, Value v1, Value v2) {
        ShiftExp.Op op = (ShiftExp.Op) operator;
        int a = v1.getConstant();
        int b = v2.getConstant();
        return switch (op) {
            case SHL -> Value.makeConstant(a << b);
            case SHR -> Value.makeConstant(a >> b);
            case USHR -> Value.makeConstant(a >>> b);
        };
    }

    private static Value bitwiseEvaluate(BinaryExp.Op operator, Value v1, Value v2) {
        BitwiseExp.Op op = (BitwiseExp.Op) operator;
        int a = v1.getConstant();
        int b = v2.getConstant();
        return switch (op) {
            case OR -> Value.makeConstant(a | b);
            case AND -> Value.makeConstant(a & b);
            case XOR -> Value.makeConstant(a ^ b);
        };
    }

    private static Value arithmeticEvaluate(BinaryExp.Op operator, Value v1, Value v2) {
        ArithmeticExp.Op op = (ArithmeticExp.Op) operator;
        int a = v1.getConstant();
        int b = v2.getConstant();
        return switch (op) {
            case ADD -> Value.makeConstant(a + b);
            case SUB -> Value.makeConstant(a - b);
            case MUL -> Value.makeConstant(a * b);
            case DIV -> {
                if (b == 0) yield Value.getUndef();
                yield Value.makeConstant(a / b);
            }
            case REM -> {
                if (b == 0) yield Value.getUndef();
                yield Value.makeConstant(a % b);
            }
        };
    }
}
