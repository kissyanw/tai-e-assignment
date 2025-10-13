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
import pascal.taie.ir.stmt.*;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.Objects;

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
        for(Var var: cfg.getIR().getVars()) {
            if (canHoldInt(var)) fact.update(var, Value.getUndef());
        }
        for (Var param : cfg.getIR().getParams()) {
            if (canHoldInt(param)) fact.update(param, Value.getNAC());
        }
        if (canHoldInt(Objects.requireNonNull(cfg.getIR().getThis()))) fact.update(cfg.getIR().getThis(), Value.getNAC());
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
        for (Var var: fact.keySet()) {
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isNAC() || v2.isNAC()) return Value.getNAC();
        else if (v1.isUndef()) return v2;
        else if (v2.isUndef()) return v1;
        else if (v1.equals(v2)) return v1;
        else return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact newOut = in.copy();
        if(stmt instanceof DefinitionStmt<?,?> definitionStmt) {
            if (definitionStmt instanceof AssignStmt<?,?> assignStmt) {
                LValue l = assignStmt.getLValue();
                RValue r = assignStmt.getRValue();
                if (l instanceof Var lvar) {
                    if (canHoldInt(lvar)) {
                        newOut.update(lvar, evaluate(r, in));
                        return out.copyFrom(newOut);
                    }
                    else return false; //handle non-int-lval as no change
                }
                else return false; //handle store... as no change
            }
            else if (definitionStmt instanceof Invoke invokeStmt) {
                return false;// handle invoke as no change
            }
            else {
                return false; //handle other definition-stmt as no change
            }
        }
        else {
            return false; //handle non-definition-stmt as no change
        }

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
        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        else if (exp instanceof Var var) {
            return in.get(var);
        }
        else if (exp instanceof BinaryExp binaryExp) {
            Var var1 = binaryExp.getOperand1();
            Var var2 = binaryExp.getOperand2();
            Value v1= in.get(var1);
            Value v2= in.get(var2);
            if (v1.isUndef() || v2.isUndef()) return Value.getUndef();
            else if (v1.isNAC() || v2.isNAC()) {
                if (v2.isConstant() && v2.getConstant() == 0 && binaryExp instanceof ArithmeticExp arithmeticExp) {
                    ArithmeticExp.Op op = arithmeticExp.getOperator();
                    if (op == ArithmeticExp.Op.DIV || op ==  ArithmeticExp.Op.REM) return Value.getUndef();
                    else return Value.getNAC();
                }
                return Value.getNAC();
            }
            else {
                if (binaryExp instanceof ArithmeticExp arithmeticExp) return evaluateArithmeticExp(arithmeticExp, in);
                else if (binaryExp instanceof  BitwiseExp bitwiseExp) return evaluateBitwiseExp(bitwiseExp, in);
                else if (binaryExp instanceof ShiftExp shiftExp) return evaluateShiftExp(shiftExp, in);
                else if (binaryExp instanceof ConditionExp conditionExp) return evaluateConditionExp(conditionExp, in);
                else return Value.getNAC();
            }
        }
        else if (exp instanceof FieldAccess fieldAccess) {
            //todo
            return Value.getNAC();
        }
        else if (exp instanceof ArrayAccess arrayAccess) {
            //todo
            return Value.getNAC();
        }
        else return Value.getNAC();
    }

    private static Value evaluateArithmeticExp(ArithmeticExp arithmeticExp, CPFact in) {
        ArithmeticExp.Op op = arithmeticExp.getOperator();
        return switch (op) {
            case ADD ->
                    Value.makeConstant(in.get(arithmeticExp.getOperand1()).getConstant() + in.get(arithmeticExp.getOperand2()).getConstant());
            case SUB ->
                    Value.makeConstant(in.get(arithmeticExp.getOperand1()).getConstant() - in.get(arithmeticExp.getOperand2()).getConstant());
            case MUL ->
                    Value.makeConstant(in.get(arithmeticExp.getOperand1()).getConstant() * in.get(arithmeticExp.getOperand2()).getConstant());
            case DIV -> {
                if (in.get(arithmeticExp.getOperand2()).getConstant() == 0) yield Value.getUndef();
                yield Value.makeConstant(in.get(arithmeticExp.getOperand1()).getConstant() / in.get(arithmeticExp.getOperand2()).getConstant());
            }
            case REM -> {
                if (in.get(arithmeticExp.getOperand2()).getConstant() == 0) yield Value.getUndef();
                yield Value.makeConstant(in.get(arithmeticExp.getOperand1()).getConstant() % in.get(arithmeticExp.getOperand2()).getConstant());
            }
        };


    }

    private static Value evaluateBitwiseExp(BitwiseExp bitwiseExp, CPFact in) {
        BitwiseExp.Op op = bitwiseExp.getOperator();
        return switch(op) {
            case AND ->
                    Value.makeConstant(in.get(bitwiseExp.getOperand1()).getConstant() & in.get(bitwiseExp.getOperand2()).getConstant());
            case OR ->
                    Value.makeConstant(in.get(bitwiseExp.getOperand1()).getConstant() | in.get(bitwiseExp.getOperand2()).getConstant());
            case XOR ->
                    Value.makeConstant(in.get(bitwiseExp.getOperand1()).getConstant() ^ in.get(bitwiseExp.getOperand2()).getConstant());
        };
    }

    private static Value evaluateShiftExp(ShiftExp shiftExp, CPFact in) {
        ShiftExp.Op op = shiftExp.getOperator();
        return switch(op) {
            case SHL ->
                    Value.makeConstant(in.get(shiftExp.getOperand1()).getConstant() << in.get(shiftExp.getOperand2()).getConstant());
            case SHR ->
                    Value.makeConstant(in.get(shiftExp.getOperand1()).getConstant() >> in.get(shiftExp.getOperand2()).getConstant());
            case USHR ->
                    Value.makeConstant(in.get(shiftExp.getOperand1()).getConstant() >>> in.get(shiftExp.getOperand2()).getConstant());
        };
    }

    private static Value evaluateConditionExp(ConditionExp conditionExp, CPFact in) {
        ConditionExp.Op op = conditionExp.getOperator();
        return switch(op) {
            case EQ -> {
                if (in.get(conditionExp.getOperand1()).getConstant() == in.get(conditionExp.getOperand2()).getConstant())
                    yield Value.makeConstant(1);
                else yield Value.makeConstant(0);
            }
            case NE -> {
                if (in.get(conditionExp.getOperand1()).getConstant() != in.get(conditionExp.getOperand2()).getConstant())
                    yield Value.makeConstant(1);
                else yield Value.makeConstant(0);
            }
            case LT -> {
                if (in.get(conditionExp.getOperand1()).getConstant() < in.get(conditionExp.getOperand2()).getConstant())
                    yield Value.makeConstant(1);
                else yield Value.makeConstant(0);
            }
            case LE -> {
                if (in.get(conditionExp.getOperand1()).getConstant() <= in.get(conditionExp.getOperand2()).getConstant())
                    yield Value.makeConstant(1);
                else yield Value.makeConstant(0);
            }
            case GT -> {
                if (in.get(conditionExp.getOperand1()).getConstant() > in.get(conditionExp.getOperand2()).getConstant())
                    yield Value.makeConstant(1);
                else yield Value.makeConstant(0);
            }
            case GE -> {
                if (in.get(conditionExp.getOperand1()).getConstant() >= in.get(conditionExp.getOperand2()).getConstant())
                    yield Value.makeConstant(1);
                else yield Value.makeConstant(0);
            }
        };
    }
}
