import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.FrameNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.ClassNode;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.zip.CRC32;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;
import java.util.zip.ZipOutputStream;

/**
 * Replaces only zKoth's six-argument progress-bar method with a bounded version.
 *
 * <p>The patcher reads the input jar without modifying it, writes a temporary
 * output, verifies the result, and then moves that output to the requested path.
 * The generated class keeps the source class-file version (zKoth 3.1.0 is Java
 * 8, major version 52).</p>
 */
public final class PatchZKothProgressBar {
    private static final String DEFAULT_INPUT = "zKoth-3.1.0.jar";
    private static final String DEFAULT_OUTPUT = "zKoth-3.1.0-fixed.jar";

    private static final String TARGET_CLASS = "fr/maxlego08/koth/zcore/utils/ZUtils.class";
    private static final String TARGET_OWNER = "fr/maxlego08/koth/zcore/utils/ZUtils";
    private static final String TARGET_METHOD = "getProgressBar";
    private static final String TARGET_DESCRIPTOR =
            "(IIICLjava/lang/String;Ljava/lang/String;)Ljava/lang/String;";

    private PatchZKothProgressBar() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length > 2) {
            throw new IllegalArgumentException(
                    "Usage: java PatchZKothProgressBar [input.jar] [output.jar]");
        }

        Path input = Paths.get(args.length >= 1 ? args[0] : DEFAULT_INPUT)
                .toAbsolutePath().normalize();
        Path output = Paths.get(args.length >= 2 ? args[1] : DEFAULT_OUTPUT)
                .toAbsolutePath().normalize();

        requireInputOutputAreDistinct(input, output);
        if (!Files.isRegularFile(input)) {
            throw new IOException("Input jar does not exist or is not a file: " + input);
        }

        byte[] sourceDigest = sha256(input);
        Path outputParent = output.getParent();
        if (outputParent == null || !Files.isDirectory(outputParent)) {
            throw new IOException("Output directory does not exist: " + outputParent);
        }

        Path temporaryOutput = Files.createTempFile(
                outputParent, output.getFileName().toString() + ".", ".tmp");
        boolean moved = false;
        try {
            PatchResult patchResult = patchJar(input, temporaryOutput);
            verifyOutput(input, temporaryOutput, patchResult);

            byte[] sourceDigestAfterPatch = sha256(input);
            if (!Arrays.equals(sourceDigest, sourceDigestAfterPatch)) {
                throw new IOException("Input jar changed while patching: " + input);
            }

            moveIntoPlace(temporaryOutput, output);
            moved = true;

            System.out.println("Patched " + TARGET_CLASS + "::" + TARGET_METHOD
                    + TARGET_DESCRIPTOR);
            System.out.println("Input : " + input);
            System.out.println("Output: " + output);
            System.out.println("Verified entries=" + patchResult.entryCount
                    + ", classVersion=" + patchResult.classVersion
                    + ", sourceUnchanged=true");
        } finally {
            if (!moved) {
                Files.deleteIfExists(temporaryOutput);
            }
        }
    }

    private static void requireInputOutputAreDistinct(Path input, Path output) throws IOException {
        if (input.equals(output)) {
            throw new IOException("Refusing to overwrite the input jar; choose a different output path");
        }
        if (Files.exists(output) && Files.isSameFile(input, output)) {
            throw new IOException("Refusing to overwrite the input jar; choose a different output path");
        }
    }

    private static PatchResult patchJar(Path input, Path output) throws IOException {
        int entryCount = 0;
        int classVersion = -1;
        boolean foundTarget = false;

        try (ZipFile inputZip = new ZipFile(input.toFile());
             OutputStream fileOutput = Files.newOutputStream(output);
             ZipOutputStream outputZip = new ZipOutputStream(fileOutput)) {

            Enumeration<? extends ZipEntry> entries = inputZip.entries();
            while (entries.hasMoreElements()) {
                ZipEntry inputEntry = entries.nextElement();
                byte[] inputBytes = readAll(inputZip.getInputStream(inputEntry));
                byte[] outputBytes = inputBytes;

                if (TARGET_CLASS.equals(inputEntry.getName())) {
                    if (inputEntry.isDirectory()) {
                        throw new IOException("Target class entry is a directory: " + TARGET_CLASS);
                    }
                    outputBytes = patchTargetClass(inputBytes);
                    classVersion = readClassVersion(outputBytes);
                    foundTarget = true;
                }

                ZipEntry outputEntry = copyEntryMetadata(inputEntry, outputBytes);
                outputZip.putNextEntry(outputEntry);
                outputZip.write(outputBytes);
                outputZip.closeEntry();
                entryCount++;
            }
        }

        if (!foundTarget) {
            throw new IOException("Missing target class entry: " + TARGET_CLASS);
        }
        return new PatchResult(entryCount, classVersion);
    }

    private static byte[] patchTargetClass(byte[] classBytes) throws IOException {
        ClassReader reader = new ClassReader(classBytes);
        ClassNode classNode = new ClassNode();
        reader.accept(classNode, 0);

        if (!TARGET_OWNER.equals(classNode.name)) {
            throw new IOException("Unexpected target class name: " + classNode.name);
        }

        MethodNode target = null;
        int matches = 0;
        for (MethodNode method : classNode.methods) {
            if (TARGET_METHOD.equals(method.name)
                    && TARGET_DESCRIPTOR.equals(method.desc)) {
                target = method;
                matches++;
            }
        }
        if (matches != 1 || target == null) {
            throw new IOException("Expected exactly one six-argument getProgressBar method, found "
                    + matches);
        }

        replaceMethodBody(target);

        // COMPUTE_FRAMES is deliberately not used: that would recompute unrelated
        // methods and may require loading Bukkit/plugin classes unavailable here.
        ClassWriter writer = new ClassWriter(0);
        classNode.accept(writer);
        byte[] patched = writer.toByteArray();

        if (readClassVersion(patched) != readClassVersion(classBytes)) {
            throw new IOException("Target class version changed during patching");
        }
        return patched;
    }

    /**
     * Builds the equivalent progress bar while making repeat counts non-negative.
     * Locals 1..6 are the original six arguments; local 7 stores completed cells.
     */
    private static void replaceMethodBody(MethodNode method) {
        InsnList instructions = new InsnList();
        LabelNode zeroTotal = new LabelNode();
        LabelNode clamp = new LabelNode();

        // if (total <= 0) completed = 0;
        instructions.add(new VarInsnNode(Opcodes.ILOAD, 2));
        instructions.add(new JumpInsnNode(Opcodes.IFLE, zeroTotal));

        // completed = (int) (length * ((float) progress / (float) total));
        instructions.add(new VarInsnNode(Opcodes.ILOAD, 3));
        instructions.add(new InsnNode(Opcodes.I2F));
        instructions.add(new VarInsnNode(Opcodes.ILOAD, 1));
        instructions.add(new InsnNode(Opcodes.I2F));
        instructions.add(new VarInsnNode(Opcodes.ILOAD, 2));
        instructions.add(new InsnNode(Opcodes.I2F));
        instructions.add(new InsnNode(Opcodes.FDIV));
        instructions.add(new InsnNode(Opcodes.FMUL));
        instructions.add(new InsnNode(Opcodes.F2I));
        instructions.add(new VarInsnNode(Opcodes.ISTORE, 7));
        instructions.add(new JumpInsnNode(Opcodes.GOTO, clamp));

        // The first frame has the original arguments only; local 7 is not live yet.
        instructions.add(zeroTotal);
        instructions.add(new FrameNode(Opcodes.F_SAME, 0, null, 0, null));
        instructions.add(new InsnNode(Opcodes.ICONST_0));
        instructions.add(new VarInsnNode(Opcodes.ISTORE, 7));

        // Both paths arrive here with local 7 initialized.
        instructions.add(clamp);
        instructions.add(new FrameNode(
                Opcodes.F_APPEND, 1, new Object[]{Opcodes.INTEGER}, 0, null));

        // completed = Math.max(0, Math.min(length, completed));
        instructions.add(new VarInsnNode(Opcodes.ILOAD, 3));
        instructions.add(new VarInsnNode(Opcodes.ILOAD, 7));
        instructions.add(new MethodInsnNode(
                Opcodes.INVOKESTATIC, "java/lang/Math", "min", "(II)I", false));
        instructions.add(new InsnNode(Opcodes.ICONST_0));
        instructions.add(new InsnNode(Opcodes.SWAP));
        instructions.add(new MethodInsnNode(
                Opcodes.INVOKESTATIC, "java/lang/Math", "max", "(II)I", false));
        instructions.add(new VarInsnNode(Opcodes.ISTORE, 7));

        // Keep the original StringBuilder/Guava construction and only change the
        // bounded count calculation above.
        instructions.add(new VarInsnNode(Opcodes.ALOAD, 0));
        instructions.add(new TypeInsnNode(Opcodes.NEW, "java/lang/StringBuilder"));
        instructions.add(new InsnNode(Opcodes.DUP));
        instructions.add(new MethodInsnNode(
                Opcodes.INVOKESPECIAL, "java/lang/StringBuilder", "<init>", "()V", false));

        addRepeatedSegment(instructions, 5, 4);
        instructions.add(new VarInsnNode(Opcodes.ILOAD, 7));
        instructions.add(new MethodInsnNode(
                Opcodes.INVOKESTATIC, "com/google/common/base/Strings", "repeat",
                "(Ljava/lang/String;I)Ljava/lang/String;", false));
        instructions.add(new MethodInsnNode(
                Opcodes.INVOKEVIRTUAL, "java/lang/StringBuilder", "append",
                "(Ljava/lang/String;)Ljava/lang/StringBuilder;", false));

        addRepeatedSegment(instructions, 6, 4);
        instructions.add(new VarInsnNode(Opcodes.ILOAD, 3));
        instructions.add(new VarInsnNode(Opcodes.ILOAD, 7));
        instructions.add(new InsnNode(Opcodes.ISUB));
        instructions.add(new MethodInsnNode(
                Opcodes.INVOKESTATIC, "com/google/common/base/Strings", "repeat",
                "(Ljava/lang/String;I)Ljava/lang/String;", false));
        instructions.add(new MethodInsnNode(
                Opcodes.INVOKEVIRTUAL, "java/lang/StringBuilder", "append",
                "(Ljava/lang/String;)Ljava/lang/StringBuilder;", false));

        instructions.add(new MethodInsnNode(
                Opcodes.INVOKEVIRTUAL, "java/lang/StringBuilder", "toString",
                "()Ljava/lang/String;", false));
        instructions.add(new MethodInsnNode(
                Opcodes.INVOKEVIRTUAL, TARGET_OWNER, "color",
                "(Ljava/lang/String;)Ljava/lang/String;", false));
        instructions.add(new InsnNode(Opcodes.ARETURN));

        method.instructions = instructions;
        method.tryCatchBlocks.clear();
        method.localVariables.clear();
        method.maxStack = 5;
        method.maxLocals = 8;
    }

    /** Leaves a repeated color+symbol segment on the operand stack. */
    private static void addRepeatedSegment(InsnList instructions, int colorLocal, int symbolLocal) {
        instructions.add(new TypeInsnNode(Opcodes.NEW, "java/lang/StringBuilder"));
        instructions.add(new InsnNode(Opcodes.DUP));
        instructions.add(new MethodInsnNode(
                Opcodes.INVOKESPECIAL, "java/lang/StringBuilder", "<init>", "()V", false));
        instructions.add(new VarInsnNode(Opcodes.ALOAD, colorLocal));
        instructions.add(new MethodInsnNode(
                Opcodes.INVOKEVIRTUAL, "java/lang/StringBuilder", "append",
                "(Ljava/lang/String;)Ljava/lang/StringBuilder;", false));
        instructions.add(new VarInsnNode(Opcodes.ILOAD, symbolLocal));
        instructions.add(new MethodInsnNode(
                Opcodes.INVOKEVIRTUAL, "java/lang/StringBuilder", "append",
                "(C)Ljava/lang/StringBuilder;", false));
        instructions.add(new MethodInsnNode(
                Opcodes.INVOKEVIRTUAL, "java/lang/StringBuilder", "toString",
                "()Ljava/lang/String;", false));
    }

    private static void verifyOutput(Path input, Path output, PatchResult patchResult)
            throws IOException {
        List<String> inputNames = new ArrayList<String>();
        List<String> outputNames = new ArrayList<String>();
        Set<String> seenInputNames = new HashSet<String>();
        Set<String> seenOutputNames = new HashSet<String>();

        try (ZipFile inputZip = new ZipFile(input.toFile());
             ZipFile outputZip = new ZipFile(output.toFile())) {
            Enumeration<? extends ZipEntry> inputEntries = inputZip.entries();
            while (inputEntries.hasMoreElements()) {
                ZipEntry inputEntry = inputEntries.nextElement();
                String name = inputEntry.getName();
                if (!seenInputNames.add(name)) {
                    throw new IOException("Duplicate input entry: " + name);
                }
                inputNames.add(name);

                ZipEntry outputEntry = outputZip.getEntry(name);
                if (outputEntry == null) {
                    throw new IOException("Output is missing entry: " + name);
                }
                if (!TARGET_CLASS.equals(name)) {
                    byte[] before = readAll(inputZip.getInputStream(inputEntry));
                    byte[] after = readAll(outputZip.getInputStream(outputEntry));
                    if (!Arrays.equals(before, after)) {
                        throw new IOException("Unchanged entry differs: " + name);
                    }
                }
            }

            Enumeration<? extends ZipEntry> outputEntries = outputZip.entries();
            while (outputEntries.hasMoreElements()) {
                String name = outputEntries.nextElement().getName();
                if (!seenOutputNames.add(name)) {
                    throw new IOException("Duplicate output entry: " + name);
                }
                outputNames.add(name);
            }

            if (!inputNames.equals(outputNames)) {
                throw new IOException("Output entry order/set differs from input");
            }

            ZipEntry targetEntry = outputZip.getEntry(TARGET_CLASS);
            if (targetEntry == null) {
                throw new IOException("Output is missing target class: " + TARGET_CLASS);
            }
            verifyPatchedClass(readAll(outputZip.getInputStream(targetEntry)), patchResult.classVersion);
        }
    }

    private static void verifyPatchedClass(byte[] classBytes, int expectedVersion) throws IOException {
        if (readClassVersion(classBytes) != expectedVersion || expectedVersion > Opcodes.V1_8) {
            throw new IOException("Output target class is not Java 8-compatible");
        }

        ClassNode classNode = new ClassNode();
        new ClassReader(classBytes).accept(classNode, 0);
        int targetMethods = 0;
        int repeatCalls = 0;
        int minCalls = 0;
        int maxCalls = 0;

        for (MethodNode method : classNode.methods) {
            if (!TARGET_METHOD.equals(method.name) || !TARGET_DESCRIPTOR.equals(method.desc)) {
                continue;
            }
            targetMethods++;
            for (org.objectweb.asm.tree.AbstractInsnNode instruction : method.instructions) {
                if (!(instruction instanceof MethodInsnNode)) {
                    continue;
                }
                MethodInsnNode call = (MethodInsnNode) instruction;
                if (Opcodes.INVOKESTATIC == call.getOpcode()
                        && "com/google/common/base/Strings".equals(call.owner)
                        && "repeat".equals(call.name)
                        && "(Ljava/lang/String;I)Ljava/lang/String;".equals(call.desc)) {
                    repeatCalls++;
                }
                if (Opcodes.INVOKESTATIC == call.getOpcode()
                        && "java/lang/Math".equals(call.owner)
                        && "min".equals(call.name)
                        && "(II)I".equals(call.desc)) {
                    minCalls++;
                }
                if (Opcodes.INVOKESTATIC == call.getOpcode()
                        && "java/lang/Math".equals(call.owner)
                        && "max".equals(call.name)
                        && "(II)I".equals(call.desc)) {
                    maxCalls++;
                }
            }
        }

        if (targetMethods != 1 || repeatCalls != 2 || minCalls != 1 || maxCalls != 1) {
            throw new IOException("Output target method does not contain the expected bounded implementation"
                    + " (methods=" + targetMethods + ", repeat=" + repeatCalls
                    + ", min=" + minCalls + ", max=" + maxCalls + ")");
        }
    }

    private static ZipEntry copyEntryMetadata(ZipEntry inputEntry, byte[] outputBytes) {
        ZipEntry outputEntry = new ZipEntry(inputEntry);
        if (inputEntry.getMethod() == ZipEntry.STORED) {
            CRC32 crc = new CRC32();
            crc.update(outputBytes);
            outputEntry.setSize(outputBytes.length);
            outputEntry.setCompressedSize(outputBytes.length);
            outputEntry.setCrc(crc.getValue());
        }
        return outputEntry;
    }

    private static void moveIntoPlace(Path temporaryOutput, Path output) throws IOException {
        try {
            Files.move(temporaryOutput, output,
                    StandardCopyOption.ATOMIC_MOVE, StandardCopyOption.REPLACE_EXISTING);
        } catch (AtomicMoveNotSupportedException e) {
            Files.move(temporaryOutput, output, StandardCopyOption.REPLACE_EXISTING);
        }
    }

    private static byte[] readAll(InputStream input) throws IOException {
        try (InputStream stream = input;
             ByteArrayOutputStream output = new ByteArrayOutputStream()) {
            byte[] buffer = new byte[8192];
            int read;
            while ((read = stream.read(buffer)) != -1) {
                output.write(buffer, 0, read);
            }
            return output.toByteArray();
        }
    }

    private static int readClassVersion(byte[] classBytes) throws IOException {
        if (classBytes.length < 8
                || (classBytes[0] & 0xff) != 0xca
                || (classBytes[1] & 0xff) != 0xfe
                || (classBytes[2] & 0xff) != 0xba
                || (classBytes[3] & 0xff) != 0xbe) {
            throw new IOException("Invalid class file");
        }
        return ((classBytes[6] & 0xff) << 8) | (classBytes[7] & 0xff);
    }

    private static byte[] sha256(Path file) throws IOException {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            try (InputStream input = Files.newInputStream(file)) {
                byte[] buffer = new byte[8192];
                int read;
                while ((read = input.read(buffer)) != -1) {
                    digest.update(buffer, 0, read);
                }
            }
            return digest.digest();
        } catch (NoSuchAlgorithmException e) {
            throw new AssertionError("SHA-256 is required by every Java runtime", e);
        }
    }

    private static final class PatchResult {
        private final int entryCount;
        private final int classVersion;

        private PatchResult(int entryCount, int classVersion) {
            this.entryCount = entryCount;
            this.classVersion = classVersion;
        }
    }
}

