package soot.asm;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 1997 - 2014 Raja Vallee-Rai and others
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 2.1 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Lesser Public License for more details.
 * 
 * You should have received a copy of the GNU General Lesser Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/lgpl-2.1.html>.
 * #L%
 */
import org.objectweb.asm.AnnotationVisitor;
import org.objectweb.asm.Attribute;
import org.objectweb.asm.Handle;
import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.TypePath;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.MethodNode;

import java.util.HashMap;

import soot.ArrayType;
import soot.RefType;
import soot.SootMethod;
import soot.Type;
import soot.options.Options;
import soot.tagkit.AnnotationConstants;
import soot.tagkit.AnnotationDefaultTag;
import soot.tagkit.AnnotationTag;
import soot.tagkit.BytecodeOffsetTag;
import soot.tagkit.VisibilityAnnotationTag;
import soot.tagkit.VisibilityParameterAnnotationTag;
/**
 * Soot method builder.
 *
 * @author Aaloan Miftah
 */
class MethodBuilder extends MethodNode implements Opcodes {

  private TagBuilder tb;
  private VisibilityAnnotationTag[] visibleParamAnnotations;
  private VisibilityAnnotationTag[] invisibleParamAnnotations;
  private final SootMethod method;
  private final SootClassBuilder scb;
  private MethodVisitor mv;
  private HashMap<AbstractInsnNode, Integer> offsetLookup = new HashMap<AbstractInsnNode, Integer>();
  private int ldcStringCount;

  MethodBuilder(SootMethod method, SootClassBuilder scb, String desc, String[] ex, MethodVisitor mv) {
    super(Opcodes.ASM5, method.getModifiers(), method.getName(), desc, null, ex);
    this.method = method;
    this.scb = scb;
    this.mv = mv;
    ldcStringCount = 0;
  }

  private TagBuilder getTagBuilder() {
    TagBuilder t = tb;
    if (t == null) {
      t = tb = new TagBuilder(method, scb);
    }
    return t;
  }

  @Override
  public AnnotationVisitor visitAnnotation(String desc, boolean visible) {
    return getTagBuilder().visitAnnotation(desc, visible);
  }

  @Override
  public AnnotationVisitor visitAnnotationDefault() {
    return new AnnotationElemBuilder(1) {
      @Override
      public void visitEnd() {
        method.addTag(new AnnotationDefaultTag(elems.get(0)));
      }
    };
  }

  @Override
  public void visitAttribute(Attribute attr) {
    mv.visitAttribute(attr);
    getTagBuilder().visitAttribute(attr);
  }

  @Override
  public AnnotationVisitor visitParameterAnnotation(int parameter, final String desc, boolean visible) {
    VisibilityAnnotationTag vat, vats[];
    if (visible) {
      vats = visibleParamAnnotations;
      if (vats == null) {
        vats = new VisibilityAnnotationTag[method.getParameterCount()];
        visibleParamAnnotations = vats;
      }
      vat = vats[parameter];
      if (vat == null) {
        vat = new VisibilityAnnotationTag(AnnotationConstants.RUNTIME_VISIBLE);
        vats[parameter] = vat;
      }
    } else {
      vats = invisibleParamAnnotations;
      if (vats == null) {
        vats = new VisibilityAnnotationTag[method.getParameterCount()];
        invisibleParamAnnotations = vats;
      }
      vat = vats[parameter];
      if (vat == null) {
        vat = new VisibilityAnnotationTag(AnnotationConstants.RUNTIME_INVISIBLE);
        vats[parameter] = vat;
      }
    }
    final VisibilityAnnotationTag _vat = vat;
    return new AnnotationElemBuilder() {
      @Override
      public void visitEnd() {
        AnnotationTag annotTag = new AnnotationTag(desc, elems);
        _vat.addAnnotation(annotTag);
      }
    };
  }

  @Override
  public void visitTypeInsn(int op, String t) {
    super.visitTypeInsn(op, t);
    mv.visitTypeInsn(op, t);
    Type rt = AsmUtil.toJimpleRefType(t);
    if (rt instanceof ArrayType) {
      scb.addDep(((ArrayType) rt).baseType);
    } else {
      scb.addDep(rt);
    }
  }

  @Override
  public void visitFieldInsn(int opcode, String owner, String name, String desc) {
    super.visitFieldInsn(opcode, owner, name, desc);
    mv.visitFieldInsn(opcode, owner, name, desc);
    for (Type t : AsmUtil.toJimpleDesc(desc)) {
      if (t instanceof RefType) {
        scb.addDep(t);
      }
    }

    scb.addDep(AsmUtil.toQualifiedName(owner));
  }

  @Override
  public void visitMethodInsn(int opcode, String owner, String name, String desc, boolean isInterf) {
    super.visitMethodInsn(opcode, owner, name, desc, isInterf);

    if (Options.v().keep_offset() && opcode == INVOKEVIRTUAL) {
      AbstractInsnNode offsetKey = instructions.getLast();
      Label here = new Label();
      visitLabel(here);
      offsetLookup.put(offsetKey, new Integer(here.getOffset() - ldcStringCount));
    }
    mv.visitMethodInsn(opcode, owner, name, desc, isInterf);

    for (Type t : AsmUtil.toJimpleDesc(desc)) {
      addDeps(t);
    }

    scb.addDep(AsmUtil.toBaseType(owner));
  }

  @Override
  public void visitLdcInsn(Object cst) {
    super.visitLdcInsn(cst);
    mv.visitLdcInsn(cst);

    if (cst instanceof Handle) {
      Handle methodHandle = (Handle) cst;
      scb.addDep(AsmUtil.toBaseType(methodHandle.getOwner()));
    }

    if (cst instanceof String) {
      ++ldcStringCount;
    }
  }

  private void addDeps(Type t) {
    if (t instanceof RefType) {
      scb.addDep(t);
    } else if (t instanceof ArrayType) {
      ArrayType at = (ArrayType) t;
      addDeps(at.getElementType());
    }
  }

  @Override
  public void visitTryCatchBlock(Label start, Label end, Label handler, String type) {
    super.visitTryCatchBlock(start, end, handler, type);
    mv.visitTryCatchBlock(start, end, handler, type);
    if (type != null) {
      scb.addDep(AsmUtil.toQualifiedName(type));
    }
  }

  @Override
  public void visitEnd() {
    super.visitEnd();
    if (visibleParamAnnotations != null) {
      VisibilityParameterAnnotationTag tag
          = new VisibilityParameterAnnotationTag(visibleParamAnnotations.length, AnnotationConstants.RUNTIME_VISIBLE);
      for (VisibilityAnnotationTag vat : visibleParamAnnotations) {
        tag.addVisibilityAnnotation(vat);
      }
      method.addTag(tag);
    }
    if (invisibleParamAnnotations != null) {
      VisibilityParameterAnnotationTag tag
          = new VisibilityParameterAnnotationTag(invisibleParamAnnotations.length, AnnotationConstants.RUNTIME_INVISIBLE);
      for (VisibilityAnnotationTag vat : invisibleParamAnnotations) {
        tag.addVisibilityAnnotation(vat);
      }
      method.addTag(tag);
    }
    if (method.isConcrete()) {
      method.setSource(new AsmMethodSource(maxLocals, instructions, localVariables, tryCatchBlocks, offsetLookup));
    }
  }

  @Override
  public void visitFrame(int type, int nLocal, Object[] local, int nStack, Object[] stack) {
    super.visitFrame(type, nLocal, local, nStack, stack);
    mv.visitFrame(type, nLocal, local, nStack, stack);
  }

  @Override
  public void visitIincInsn(int var, int increment) {
    super.visitIincInsn(var, increment);
    mv.visitIincInsn(var, increment);
  }

  @Override
  public void visitInsn(int opcode) {
    super.visitInsn(opcode);
    mv.visitInsn(opcode);
  }

  @Override
  public void visitIntInsn(int opcode, int operand) {
    super.visitIntInsn(opcode, operand);
    mv.visitIntInsn(opcode, operand);
  }

  @Override
  public void visitInvokeDynamicInsn(String name, String desc, Handle bsm, Object... bsmArgs) {
    super.visitInvokeDynamicInsn(name, desc, bsm, bsmArgs);
    mv.visitInvokeDynamicInsn(name, desc, bsm, bsmArgs);
  }

  @Override
  public void visitJumpInsn(int opcode, Label label) {
    super.visitJumpInsn(opcode, label);
    mv.visitJumpInsn(opcode, label);
  }

  @Override
  public void visitLabel(Label label) {
    super.visitLabel(label);
    mv.visitLabel(label);
  }

  @Override
  public void visitLineNumber(int line, Label start) {
    super.visitLineNumber(line, start);
    mv.visitLineNumber(line, start);
  }

  @Override
  public void visitLocalVariable(String name, String desc, String signature, Label start, Label end, int index) {
    super.visitLocalVariable(name, desc, signature, start, end, index);
    mv.visitLocalVariable(name, desc, signature, start, end, index);
  }

  @Override
  public void visitLookupSwitchInsn(Label dflt, int[] keys, Label[] labels) {
    super.visitLookupSwitchInsn(dflt, keys, labels);
    mv.visitLookupSwitchInsn(dflt, keys, labels);
  }

  @Override
  public void visitMaxs(int maxStack, int maxLocals) {
    super.visitMaxs(maxStack, maxLocals);
    mv.visitMaxs(maxStack, maxLocals);
  }

  @Override
  public void visitMultiANewArrayInsn(String desc, int dims) {
    super.visitMultiANewArrayInsn(desc, dims);
    mv.visitMultiANewArrayInsn(desc, dims);
  }

  @Override
  public void visitParameter(String name, int access) {
    super.visitParameter(name, access);
    mv.visitParameter(name, access);
  }

  @Override
  public void visitTableSwitchInsn(int min, int max, Label dflt, Label... labels) {
    super.visitTableSwitchInsn(min, max, dflt, labels);
    mv.visitTableSwitchInsn(min, max, dflt, labels);
  }

  @Override
  public void visitVarInsn(int opcode, int var) {
    super.visitVarInsn(opcode, var);
    mv.visitVarInsn(opcode, var);
  }
}
