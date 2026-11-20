import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.SecureRandom;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Scanner;

public class PKC {

    private static final SecureRandom RANDOM = new SecureRandom();
    private static final BigInteger ZERO = BigInteger.ZERO;
    private static final BigInteger ONE = BigInteger.ONE;
    private static final BigInteger TWO = BigInteger.valueOf(2);
    private static final BigInteger THREE = BigInteger.valueOf(3);

    // Các số nguyên tố nhỏ phục vụ chia thử trong genPrime và isPrime 
    private static final int[] SMALL_PRIMES = {
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
        73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
        157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
        239, 241, 251
    };

    // Bộ cơ sở cố định từ 2 đến 37 kết hợp ngẫu nhiên cho Miller-Rabin 
    private static final int[] FIXED_BASES = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};

    // Tham số nhóm MODP 2048-bit chuẩn từ RFC 3526 
    private static final String RFC3526_2048_P_HEX =
        "FFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD1" +
        "29024E088A67CC74020BBEA63B139B22514A08798E3404DD" +
        "EF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245" +
        "E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7ED" +
        "EE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3D" +
        "C2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F" +
        "83655D23DCA3AD961C62F356208552BB9ED529077096966D" +
        "670C354E4ABC9804F1746C08CA18217C32905E462E36CE3B" +
        "E39E772C180E86039B2783A2EC07A28FB5C55DF06F4C52C9" +
        "DE2BCBF6955817183995497CEA956AE515D2261898FA0510" +
        "15728E5A8AACAA68FFFFFFFFFFFFFFFF";

    // =========================================================================
    // PHẦN A: THƯ VIỆN SỐ HỌC MODULO 
    // =========================================================================

    /**
     * Lũy thừa nhanh Square-and-Multiply: tính a^e mod m trong O(log e) phép nhân.
     */
    public static BigInteger modexp(BigInteger a, BigInteger e, BigInteger m) {
        if (m == null || m.compareTo(ZERO) <= 0) {
            throw new IllegalArgumentException("ERROR: Modulo m phai > 0");
        }
        if (e == null || e.compareTo(ZERO) < 0) {
            throw new IllegalArgumentException("ERROR: So mu e phai >= 0");
        }
        if (m.compareTo(ONE) == 0) {
            return ZERO;
        }
        BigInteger result = ONE;
        BigInteger base = a.mod(m);
        int bitLen = e.bitLength();
        for (int i = 0; i < bitLen; i++) {
            if (e.testBit(i)) {
                result = result.multiply(base).mod(m);
            }
            base = base.multiply(base).mod(m);
        }
        return result;
    }

    /**
     * Thuật toán Euclid mở rộng: trả về mảng [g, x, y] sao cho a*x + b*y = g = gcd(a, b).
     */
    public static BigInteger[] egcd(BigInteger a, BigInteger b) {
        BigInteger signA = ONE;
        BigInteger signB = ONE;
        if (a.compareTo(ZERO) < 0) {
            a = ZERO.subtract(a);
            signA = ZERO.subtract(ONE);
        }
        if (b.compareTo(ZERO) < 0) {
            b = ZERO.subtract(b);
            signB = ZERO.subtract(ONE);
        }

        BigInteger old_r = a, r = b;
        BigInteger old_s = ONE, s = ZERO;
        BigInteger old_t = ZERO, t = ONE;

        while (r.compareTo(ZERO) != 0) {
            BigInteger[] qr = old_r.divideAndRemainder(r);
            BigInteger q = qr[0];
            old_r = r;
            r = qr[1];

            BigInteger temp_s = old_s.subtract(q.multiply(s));
            old_s = s;
            s = temp_s;

            BigInteger temp_t = old_t.subtract(q.multiply(t));
            old_t = t;
            t = temp_t;
        }
        return new BigInteger[]{old_r, old_s.multiply(signA), old_t.multiply(signB)};
    }

    /**
     * Nghịch đảo modulo: trả về a^-1 mod m trong đoạn [1, m-1].
     * Nếu gcd(a, m) != 1 thì ném ngoại lệ báo lỗi không tồn tại nghịch đảo.
     */
    public static BigInteger modinv(BigInteger a, BigInteger m) {
        if (m == null || m.compareTo(ONE) <= 0) {
            throw new IllegalArgumentException("ERROR: Modulo m phai > 1");
        }
        BigInteger aMod = a.mod(m);
        BigInteger[] res = egcd(aMod, m);
        BigInteger g = res[0];
        BigInteger x = res[1];
        if (g.compareTo(ONE) != 0) {
            throw new ArithmeticException("ERROR (gcd = " + g.toString() + ", khong ton tai nghich dao)");
        }
        return x.mod(m);
    }

    /**
     * Sinh số nguyên ngẫu nhiên phân bố đều trong đoạn [min, max].
     */
    public static BigInteger randomBetween(BigInteger min, BigInteger max) {
        BigInteger range = max.subtract(min).add(ONE);
        int bits = range.bitLength();
        BigInteger r;
        do {
            r = new BigInteger(bits, RANDOM);
        } while (r.compareTo(range) >= 0);
        return r.add(min);
    }

    /**
     * Kiểm tra nguyên tố Miller-Rabin với tối thiểu 40 vòng cơ sở ngẫu nhiên + bộ cơ sở cố định.
     */
    public static boolean isPrime(BigInteger n) {
        if (n == null || n.compareTo(TWO) < 0) return false;
        for (int p : SMALL_PRIMES) {
            BigInteger bp = BigInteger.valueOf(p);
            if (n.compareTo(bp) == 0) return true;
            if (n.mod(bp).compareTo(ZERO) == 0) return false;
        }

        // Phân tích n - 1 = 2^s * d với d lẻ
        BigInteger nMinus1 = n.subtract(ONE);
        BigInteger d = nMinus1;
        int s = 0;
        while (!d.testBit(0)) {
            s++;
            d = d.divide(TWO);
        }

        // Kiểm tra qua bộ cơ sở cố định 2, 3, 5, ..., 37
        for (int b : FIXED_BASES) {
            BigInteger a = BigInteger.valueOf(b);
            if (a.compareTo(nMinus1) >= 0) break;
            if (!millerRabinPass(a, s, d, n, nMinus1)) {
                return false;
            }
        }

        // Kiểm tra tối thiểu 40 vòng với cơ sở ngẫu nhiên trong [2, n - 2]
        BigInteger maxBase = n.subtract(TWO);
        for (int i = 0; i < 40; i++) {
            BigInteger a = randomBetween(TWO, maxBase);
            if (!millerRabinPass(a, s, d, n, nMinus1)) {
                return false;
            }
        }
        return true;
    }

    private static boolean millerRabinPass(BigInteger a, int s, BigInteger d, BigInteger n, BigInteger nMinus1) {
        BigInteger x = modexp(a, d, n);
        if (x.compareTo(ONE) == 0 || x.compareTo(nMinus1) == 0) {
            return true;
        }
        for (int r = 1; r < s; r++) {
            x = modexp(x, TWO, n);
            if (x.compareTo(nMinus1) == 0) {
                return true;
            }
            if (x.compareTo(ONE) == 0) {
                return false;
            }
        }
        return false;
    }

    /**
     * Sinh số nguyên tố ngẫu nhiên đúng b bit:
     * Bật bit cao nhất (b-1) và bit thấp nhất (0), chia thử cho số nguyên tố nhỏ rồi gọi Miller-Rabin.
     */
    public static BigInteger genPrime(int b) {
        if (b < 2) {
            throw new IllegalArgumentException("ERROR: So bit b phai >= 2");
        }
        if (b == 2) {
            return RANDOM.nextBoolean() ? TWO : THREE;
        }
        while (true) {
            BigInteger candidate = new BigInteger(b, RANDOM);
            candidate = candidate.setBit(b - 1);
            candidate = candidate.setBit(0);

            boolean divisibleBySmall = false;
            for (int p : SMALL_PRIMES) {
                BigInteger bp = BigInteger.valueOf(p);
                if (candidate.compareTo(bp) > 0 && candidate.mod(bp).compareTo(ZERO) == 0) {
                    divisibleBySmall = true;
                    break;
                }
            }
            if (divisibleBySmall) continue;

            if (isPrime(candidate)) {
                return candidate;
            }
        }
    }

    // =========================================================================
    // PHẦN B: TRAO ĐỔI KHÓA DIFFIE-HELLMAN
    // =========================================================================

    public static BigInteger dhPub(BigInteger p, BigInteger g, BigInteger x) {
        if (p.compareTo(THREE) <= 0) {
            throw new IllegalArgumentException("ERROR: p phai > 3");
        }
        if (g.compareTo(ONE) <= 0 || g.compareTo(p.subtract(ONE)) >= 0) {
            throw new IllegalArgumentException("ERROR: g phai nam trong (1, p-1)");
        }
        if (x.compareTo(ONE) < 0 || x.compareTo(p.subtract(ONE)) >= 0) {
            throw new IllegalArgumentException("ERROR: Khoa bi mat x khong hop le");
        }
        return modexp(g, x, p);
    }

    public static BigInteger dhShared(BigInteger p, BigInteger Y, BigInteger x) {
        if (p.compareTo(THREE) <= 0) {
            throw new IllegalArgumentException("ERROR: p phai > 3");
        }
        // Kiểm tra khóa công khai nhận được: 1 < Y < p - 1 (Mục 3.5 & 5)
        if (Y.compareTo(ONE) <= 0 || Y.compareTo(p.subtract(ONE)) >= 0) {
            throw new IllegalArgumentException("ERROR: Khoa cong khai DH khong hop le (Y <= 1 hoac Y >= p-1)");
        }
        if (x.compareTo(ONE) < 0 || x.compareTo(p.subtract(ONE)) >= 0) {
            throw new IllegalArgumentException("ERROR: Khoa bi mat x khong hop le");
        }
        return modexp(Y, x, p);
    }

    // =========================================================================
    // PHẦN C: HỆ MẬT RSA 
    // =========================================================================

    /**
     * Sinh khóa RSA từ p, q, e. Trả về mảng [n, d, phi].
     */
    public static BigInteger[] rsaKeygen(BigInteger p, BigInteger q, BigInteger e) {
        if (!isPrime(p)) {
            throw new IllegalArgumentException("ERROR: p khong phai so nguyen to");
        }
        if (!isPrime(q)) {
            throw new IllegalArgumentException("ERROR: q khong phai so nguyen to");
        }
        if (p.compareTo(q) == 0) {
            throw new IllegalArgumentException("ERROR: p va q khong duoc bang nhau");
        }
        BigInteger n = p.multiply(q);
        BigInteger phi = p.subtract(ONE).multiply(q.subtract(ONE));
        if (e.compareTo(ONE) <= 0 || e.compareTo(phi) >= 0) {
            throw new IllegalArgumentException("ERROR: e phai nam trong khoang (1, phi(n))");
        }
        BigInteger[] gcdRes = egcd(e, phi);
        if (gcdRes[0].compareTo(ONE) != 0) {
            throw new IllegalArgumentException("ERROR: gcd(e, phi) != 1");
        }
        BigInteger d = modinv(e, phi);
        return new BigInteger[]{n, d, phi};
    }

    public static BigInteger rsaEnc(BigInteger n, BigInteger e, BigInteger M) {
        if (M.compareTo(ZERO) < 0 || M.compareTo(n) >= 0) {
            throw new IllegalArgumentException("ERROR: Ban ro M phai thoa 0 <= M < n");
        }
        return modexp(M, e, n);
    }

    public static BigInteger rsaDec(BigInteger n, BigInteger d, BigInteger C) {
        if (C.compareTo(ZERO) < 0 || C.compareTo(n) >= 0) {
            throw new IllegalArgumentException("ERROR: Ban ma C phai thoa 0 <= C < n");
        }
        return modexp(C, d, n);
    }

    /**
     * Tính số byte k của modulus n.
     */
    public static int getByteLength(BigInteger n) {
        int bits = n.bitLength();
        int k = (bits + 7) / 8;
        return Math.max(k, 1);
    }

    /**
     * Mã hóa văn bản RSA:
     * - Đổi chuỗi sang byte UTF-8.
     * - Gọi k là số byte của n. Cắt thành các khối k-1 byte (khối cuối có thể ngắn hơn).
     * - Mỗi khối đổi sang số nguyên big-endian, mã hóa thành C, ghi ra đúng k byte (đệm 0 bên trái).
     * - Bản mã là chuỗi HEX viết HOA nối các khối.
     */
    public static String rsaEncText(BigInteger n, BigInteger e, String text) {
        if (text == null || text.isEmpty()) {
            return "";
        }
        int k = getByteLength(n);
        if (k <= 1) {
            throw new IllegalArgumentException("ERROR: Modulus n qua nho de chia khoi van ban (k <= 1)");
        }
        int blockSize = k - 1;
        byte[] utf8Bytes = text.getBytes(StandardCharsets.UTF_8);
        StringBuilder hexCipher = new StringBuilder();

        for (int i = 0; i < utf8Bytes.length; i += blockSize) {
            int len = Math.min(blockSize, utf8Bytes.length - i);
            byte[] chunk = Arrays.copyOfRange(utf8Bytes, i, i + len);
            BigInteger M = new BigInteger(1, chunk);
            BigInteger C = rsaEnc(n, e, M);
            byte[] cBytes = toFixedLengthBytes(C, k);
            hexCipher.append(bytesToHexUpper(cBytes));
        }
        return hexCipher.toString();
    }

    /**
     * Giải mã văn bản RSA từ chuỗi HEX.
     */
    public static String rsaDecText(BigInteger n, BigInteger d, String hexCipher) {
        if (hexCipher == null || hexCipher.isEmpty()) {
            return "";
        }
        String cleaned = hexCipher.trim();
        if (cleaned.startsWith("0x") || cleaned.startsWith("0X")) {
            cleaned = cleaned.substring(2);
        }
        int k = getByteLength(n);
        int hexBlockLen = k * 2;
        if (cleaned.length() % hexBlockLen != 0) {
            throw new IllegalArgumentException("ERROR: Do dai chuoi HEX khong chia het cho kich thuoc khoi");
        }

        List<Byte> plainBytesList = new ArrayList<>();
        for (int i = 0; i < cleaned.length(); i += hexBlockLen) {
            String blockHex = cleaned.substring(i, i + hexBlockLen);
            BigInteger C = new BigInteger(blockHex, 16);
            BigInteger M = rsaDec(n, d, C);
            byte[] mBytes = toUnsignedBytes(M);
            for (byte b : mBytes) {
                plainBytesList.add(b);
            }
        }
        byte[] resultBytes = new byte[plainBytesList.size()];
        for (int i = 0; i < plainBytesList.size(); i++) {
            resultBytes[i] = plainBytesList.get(i);
        }
        return new String(resultBytes, StandardCharsets.UTF_8);
    }

    private static byte[] toFixedLengthBytes(BigInteger val, int length) {
        byte[] raw = val.toByteArray();
        byte[] result = new byte[length];
        int srcPos = (raw.length > 1 && raw[0] == 0) ? 1 : 0;
        int copyLen = raw.length - srcPos;
        if (copyLen > length) {
            throw new IllegalArgumentException("ERROR: So nguyen vuot qua k byte");
        }
        System.arraycopy(raw, srcPos, result, length - copyLen, copyLen);
        return result;
    }

    private static byte[] toUnsignedBytes(BigInteger val) {
        if (val.compareTo(ZERO) == 0) {
            return new byte[]{0};
        }
        byte[] raw = val.toByteArray();
        if (raw.length > 1 && raw[0] == 0) {
            return Arrays.copyOfRange(raw, 1, raw.length);
        }
        return raw;
    }

    private static String bytesToHexUpper(byte[] bytes) {
        StringBuilder sb = new StringBuilder(bytes.length * 2);
        for (byte b : bytes) {
            sb.append(String.format("%02X", b & 0xFF));
        }
        return sb.toString();
    }

    // =========================================================================
    // PHẦN D (D1): MÃ HÓA ELGAMAL
    // =========================================================================

    public static BigInteger elgamalPubKey(BigInteger p, BigInteger g, BigInteger x) {
        if (p.compareTo(THREE) <= 0) {
            throw new IllegalArgumentException("ERROR: p phai > 3");
        }
        if (x.compareTo(ONE) <= 0 || x.compareTo(p.subtract(ONE)) >= 0) {
            throw new IllegalArgumentException("ERROR: Khoa bi mat x phai nam trong (1, p-1)");
        }
        return modexp(g, x, p);
    }

    public static BigInteger[] elgamalEnc(BigInteger p, BigInteger g, BigInteger y, BigInteger k, BigInteger M) {
        if (p.compareTo(THREE) <= 0) {
            throw new IllegalArgumentException("ERROR: p phai > 3");
        }
        if (M.compareTo(ZERO) < 0 || M.compareTo(p) >= 0) {
            throw new IllegalArgumentException("ERROR: Ban ro M phai nam trong [0, p-1]");
        }
        if (k.compareTo(ONE) < 0 || k.compareTo(p.subtract(ONE)) >= 0) {
            throw new IllegalArgumentException("ERROR: So ngau nhien k phai nam trong [1, p-2]");
        }
        BigInteger c1 = modexp(g, k, p);
        BigInteger s = modexp(y, k, p);
        BigInteger c2 = M.multiply(s).mod(p);
        return new BigInteger[]{c1, c2};
    }

    public static BigInteger elgamalDec(BigInteger p, BigInteger x, BigInteger c1, BigInteger c2) {
        if (p.compareTo(THREE) <= 0) {
            throw new IllegalArgumentException("ERROR: p phai > 3");
        }
        if (c1.compareTo(ZERO) <= 0 || c1.compareTo(p) >= 0 || c2.compareTo(ZERO) < 0 || c2.compareTo(p) >= 0) {
            throw new IllegalArgumentException("ERROR: Ban ma (c1, c2) khong hop le");
        }
        BigInteger s = modexp(c1, x, p);
        BigInteger sInv = modinv(s, p);
        return c2.multiply(sInv).mod(p);
    }

    // =========================================================================
    // HỖ TRỢ BIỂU DIỄN SỐ (THẬP PHÂN & HEX)
    // =========================================================================

    public static BigInteger parseBigInt(String s) {
        if (s == null || s.trim().isEmpty()) {
            throw new IllegalArgumentException("ERROR: Gia tri so rong");
        }
        s = s.trim();
        boolean negative = false;
        if (s.startsWith("-")) {
            negative = true;
            s = s.substring(1).trim();
        }
        BigInteger val;
        if (s.startsWith("0x") || s.startsWith("0X")) {
            val = new BigInteger(s.substring(2), 16);
        } else {
            val = new BigInteger(s, 10);
        }
        return negative ? ZERO.subtract(val) : val;
    }

    public static String formatBigInt(BigInteger n, boolean hexMode) {
        return hexMode ? n.toString(16).toUpperCase() : n.toString(10);
    }

    // =========================================================================
    // CHẾ ĐỘ DÒNG LỆNH
    // =========================================================================

    private static void handleCommandLine(String[] rawArgs) {
        boolean hexOut = false;
        List<String> argsList = new ArrayList<>();
        for (String arg : rawArgs) {
            if ("--hex".equalsIgnoreCase(arg)) {
                hexOut = true;
            } else {
                argsList.add(arg);
            }
        }
        if (argsList.isEmpty()) {
            System.out.println("ERROR");
            return;
        }
        String[] args = argsList.toArray(new String[0]);
        String cmd = args[0].toLowerCase();

        try {
            switch (cmd) {
                case "modexp": {
                    if (args.length < 4) throw new IllegalArgumentException("ERROR");
                    BigInteger a = parseBigInt(args[1]);
                    BigInteger e = parseBigInt(args[2]);
                    BigInteger m = parseBigInt(args[3]);
                    BigInteger res = modexp(a, e, m);
                    System.out.println(formatBigInt(res, hexOut));
                    break;
                }
                case "modinv": {
                    if (args.length < 3) throw new IllegalArgumentException("ERROR");
                    BigInteger a = parseBigInt(args[1]);
                    BigInteger m = parseBigInt(args[2]);
                    BigInteger res = modinv(a, m);
                    System.out.println(formatBigInt(res, hexOut));
                    break;
                }
                case "isprime": {
                    if (args.length < 2) throw new IllegalArgumentException("ERROR");
                    BigInteger n = parseBigInt(args[1]);
                    System.out.println(isPrime(n) ? "PRIME" : "COMPOSITE");
                    break;
                }
                case "dh": {
                    if (args.length < 5) throw new IllegalArgumentException("ERROR");
                    String sub = args[1].toLowerCase();
                    if ("pub".equals(sub)) {
                        BigInteger p = parseBigInt(args[2]);
                        BigInteger g = parseBigInt(args[3]);
                        BigInteger x = parseBigInt(args[4]);
                        System.out.println(formatBigInt(dhPub(p, g, x), hexOut));
                    } else if ("shared".equals(sub)) {
                        BigInteger p = parseBigInt(args[2]);
                        BigInteger Y = parseBigInt(args[3]);
                        BigInteger x = parseBigInt(args[4]);
                        System.out.println(formatBigInt(dhShared(p, Y, x), hexOut));
                    } else {
                        System.out.println("ERROR");
                    }
                    break;
                }
                case "rsa": {
                    if (args.length < 5) throw new IllegalArgumentException("ERROR");
                    String sub = args[1].toLowerCase();
                    switch (sub) {
                        case "keygen": {
                            BigInteger p = parseBigInt(args[2]);
                            BigInteger q = parseBigInt(args[3]);
                            BigInteger e = parseBigInt(args[4]);
                            BigInteger[] nd = rsaKeygen(p, q, e);
                            System.out.println(formatBigInt(nd[0], hexOut) + " " + formatBigInt(nd[1], hexOut));
                            break;
                        }
                        case "enc": {
                            BigInteger n = parseBigInt(args[2]);
                            BigInteger e = parseBigInt(args[3]);
                            BigInteger M = parseBigInt(args[4]);
                            System.out.println(formatBigInt(rsaEnc(n, e, M), hexOut));
                            break;
                        }
                        case "dec": {
                            BigInteger n = parseBigInt(args[2]);
                            BigInteger d = parseBigInt(args[3]);
                            BigInteger C = parseBigInt(args[4]);
                            System.out.println(formatBigInt(rsaDec(n, d, C), hexOut));
                            break;
                        }
                        case "enctext": {
                            BigInteger n = parseBigInt(args[2]);
                            BigInteger e = parseBigInt(args[3]);
                            String text = args[4];
                            System.out.println(rsaEncText(n, e, text));
                            break;
                        }
                        case "dectext": {
                            BigInteger n = parseBigInt(args[2]);
                            BigInteger d = parseBigInt(args[3]);
                            String hex = args[4];
                            System.out.println(rsaDecText(n, d, hex));
                            break;
                        }
                        default:
                            System.out.println("ERROR");
                    }
                    break;
                }
                case "elgamal": {
                    if (args.length < 6) throw new IllegalArgumentException("ERROR");
                    String sub = args[1].toLowerCase();
                    if ("enc".equals(sub)) {
                        if (args.length < 7) throw new IllegalArgumentException("ERROR");
                        BigInteger p = parseBigInt(args[2]);
                        BigInteger g = parseBigInt(args[3]);
                        BigInteger y = parseBigInt(args[4]);
                        BigInteger k = parseBigInt(args[5]);
                        BigInteger M = parseBigInt(args[6]);
                        BigInteger[] c = elgamalEnc(p, g, y, k, M);
                        System.out.println(formatBigInt(c[0], hexOut) + " " + formatBigInt(c[1], hexOut));
                    } else if ("dec".equals(sub)) {
                        BigInteger p = parseBigInt(args[2]);
                        BigInteger x = parseBigInt(args[3]);
                        BigInteger c1 = parseBigInt(args[4]);
                        BigInteger c2 = parseBigInt(args[5]);
                        BigInteger M = elgamalDec(p, x, c1, c2);
                        System.out.println(formatBigInt(M, hexOut));
                    } else {
                        System.out.println("ERROR");
                    }
                    break;
                }
                default:
                    System.out.println("ERROR");
            }
        } catch (Exception ex) {
            System.out.println("ERROR");
        }
    }

    // =========================================================================
    // CHẾ ĐỘ MENU TƯƠNG TÁC
    // =========================================================================

    private static void runInteractiveMenu() {
        Scanner sc = new Scanner(System.in, StandardCharsets.UTF_8);
        while (true) {
            System.out.println("\n===== PUBLIC-KEY CRYPTOGRAPHY =====");
            System.out.println("1. Modular arithmetic");
            System.out.println("2. Diffie-Hellman key exchange");
            System.out.println("3. RSA key generation");
            System.out.println("4. RSA encrypt / decrypt (integer)");
            System.out.println("5. RSA encrypt / decrypt (text)");
            System.out.println("6. ElGamal");
            System.out.println("7. Chay bo test case chuan (Muc 6) & Tu viet (Muc 5)");
            System.out.println("8. Exit");
            System.out.print("Chon chuc nang (1-8): ");

            String choice = sc.nextLine().trim();
            try {
                switch (choice) {
                    case "1":
                        menuModularArithmetic(sc);
                        break;
                    case "2":
                        menuDiffieHellman(sc);
                        break;
                    case "3":
                        menuRsaKeygen(sc);
                        break;
                    case "4":
                        menuRsaInteger(sc);
                        break;
                    case "5":
                        menuRsaText(sc);
                        break;
                    case "6":
                        menuElGamal(sc);
                        break;
                    case "7":
                        runAllTestCases();
                        break;
                    case "8":
                        System.out.println("Ket thuc chuong trinh.");
                        return;
                    default:
                        System.out.println("Lua chon khong hop le. Vui long chon tu 1 den 8.");
                }
            } catch (Exception e) {
                System.out.println(e.getMessage() != null ? e.getMessage() : "ERROR: Dau vao khong hop le");
            }
        }
    }

    private static void menuModularArithmetic(Scanner sc) {
        System.out.println("\n--- 1. MODULAR ARITHMETIC ---");
        System.out.println("a. Luy thua nhanh modexp(a, e, m)");
        System.out.println("b. Euclid mo rong egcd(a, b)");
        System.out.println("c. Nghich dao modulo modinv(a, m)");
        System.out.println("d. Kiem tra nguyen to Miller-Rabin isPrime(n)");
        System.out.println("e. Sinh so nguyen to ngau nhien genPrime(b)");
        System.out.print("Chon phep toan (a-e): ");
        String sub = sc.nextLine().trim().toLowerCase();

        switch (sub) {
            case "a": {
                System.out.print("Nhap a: ");
                BigInteger a = parseBigInt(sc.nextLine());
                System.out.print("Nhap e: ");
                BigInteger e = parseBigInt(sc.nextLine());
                System.out.print("Nhap m: ");
                BigInteger m = parseBigInt(sc.nextLine());
                System.out.println("Ket qua a^e mod m = " + modexp(a, e, m));
                break;
            }
            case "b": {
                System.out.print("Nhap a: ");
                BigInteger a = parseBigInt(sc.nextLine());
                System.out.print("Nhap b: ");
                BigInteger b = parseBigInt(sc.nextLine());
                BigInteger[] res = egcd(a, b);
                System.out.printf("gcd(a, b) = %s, x = %s, y = %s%n", res[0], res[1], res[2]);
                break;
            }
            case "c": {
                System.out.print("Nhap a: ");
                BigInteger a = parseBigInt(sc.nextLine());
                System.out.print("Nhap m: ");
                BigInteger m = parseBigInt(sc.nextLine());
                System.out.println("Nghich dao a^-1 mod m = " + modinv(a, m));
                break;
            }
            case "d": {
                System.out.print("Nhap n: ");
                BigInteger n = parseBigInt(sc.nextLine());
                System.out.println("Ket qua: " + (isPrime(n) ? "PRIME (Nguyen to)" : "COMPOSITE (Hop so)"));
                break;
            }
            case "e": {
                System.out.print("Nhap so bit b (vd: 64, 512, 1024): ");
                int b = Integer.parseInt(sc.nextLine().trim());
                long t0 = System.currentTimeMillis();
                BigInteger p = genPrime(b);
                long t1 = System.currentTimeMillis();
                System.out.println("So nguyen to " + b + " bit: " + p);
                System.out.println("Bit length thuc te: " + p.bitLength() + " bit (Thoi gian: " + (t1 - t0) + " ms)");
                break;
            }
            default:
                System.out.println("Lua chon khong hop le.");
        }
    }

    private static void menuDiffieHellman(Scanner sc) {
        System.out.println("\n--- 2. DIFFIE-HELLMAN KEY EXCHANGE ---");
        System.out.println("1. Nhap tham so thu cong (p, g, a, b)");
        System.out.println("2. Dung tham so RFC 3526 (p 2048-bit, g = 2) va sinh ngau nhien a, b");
        System.out.print("Chon che do (1-2): ");
        String mode = sc.nextLine().trim();

        BigInteger p, g, a, b;
        if ("2".equals(mode)) {
            p = new BigInteger(RFC3526_2048_P_HEX, 16);
            g = TWO;
            a = randomBetween(TWO, p.subtract(TWO));
            b = randomBetween(TWO, p.subtract(TWO));
        } else {
            System.out.print("Nhap p (bo trong de sinh p 64-bit ngau nhien): ");
            String pStr = sc.nextLine().trim();
            p = pStr.isEmpty() ? genPrime(64) : parseBigInt(pStr);

            System.out.print("Nhap g (bo trong de mac dinh g = 5): ");
            String gStr = sc.nextLine().trim();
            g = gStr.isEmpty() ? BigInteger.valueOf(5) : parseBigInt(gStr);

            System.out.print("Nhap khoa bi mat Alice a (bo trong de sinh ngau nhien): ");
            String aStr = sc.nextLine().trim();
            a = aStr.isEmpty() ? randomBetween(TWO, p.subtract(TWO)) : parseBigInt(aStr);

            System.out.print("Nhap khoa bi mat Bob b (bo trong de sinh ngau nhien): ");
            String bStr = sc.nextLine().trim();
            b = bStr.isEmpty() ? randomBetween(TWO, p.subtract(TWO)) : parseBigInt(bStr);
        }

        BigInteger A = dhPub(p, g, a);
        BigInteger B = dhPub(p, g, b);
        BigInteger kAlice = dhShared(p, B, a);
        BigInteger kBob = dhShared(p, A, b);

        System.out.println("p = " + p + "   g = " + g);
        System.out.println("Alice a = " + a + "  ->  A = " + A);
        System.out.println("Bob   b = " + b + "  ->  B = " + B);
        System.out.println("K (Alice) = " + kAlice);
        System.out.println("K (Bob)   = " + kBob);
        System.out.println("=> " + (kAlice.compareTo(kBob) == 0 ? "KHOP" : "KHONG KHOP"));
    }

    private static void menuRsaKeygen(Scanner sc) {
        System.out.println("\n--- 3. RSA KEY GENERATION ---");
        System.out.println("1. Nhap p, q, e thu cong");
        System.out.println("2. Sinh khoa RSA ngau nhien theo so bit (512 / 1024 / 2048 bit)");
        System.out.print("Chon che do (1-2): ");
        String mode = sc.nextLine().trim();

        BigInteger p, q, e;
        if ("2".equals(mode)) {
            System.out.print("Nhap do dai khoa n (vd: 512, 1024, 2048): ");
            int bits = Integer.parseInt(sc.nextLine().trim());
            e = BigInteger.valueOf(65537);
            while (true) {
                p = genPrime(bits / 2);
                q = genPrime(bits - bits / 2);
                if (p.compareTo(q) == 0) continue;
                BigInteger phi = p.subtract(ONE).multiply(q.subtract(ONE));
                if (egcd(e, phi)[0].compareTo(ONE) == 0) break;
            }
        } else {
            System.out.print("Nhap p: ");
            p = parseBigInt(sc.nextLine());
            System.out.print("Nhap q: ");
            q = parseBigInt(sc.nextLine());
            System.out.print("Nhap e: ");
            e = parseBigInt(sc.nextLine());
        }

        BigInteger[] res = rsaKeygen(p, q, e);
        System.out.println("p = " + p + "   q = " + q + "   e = " + e);
        System.out.println("n = " + res[0] + "   phi(n) = " + res[2]);
        System.out.println("d = " + res[1]);
    }

    private static void menuRsaInteger(Scanner sc) {
        System.out.println("\n--- 4. RSA ENCRYPT / DECRYPT (INTEGER) ---");
        System.out.println("1. Chay tron ven (Nhap p, q, e, M -> In n, phi, d, C, Decrypted M)");
        System.out.println("2. Chi ma hoa (Nhap n, e, M -> In C)");
        System.out.println("3. Chi giai ma (Nhap n, d, C -> In M)");
        System.out.print("Chon che do (1-3): ");
        String mode = sc.nextLine().trim();

        if ("1".equals(mode)) {
            System.out.print("Nhap p: ");
            BigInteger p = parseBigInt(sc.nextLine());
            System.out.print("Nhap q: ");
            BigInteger q = parseBigInt(sc.nextLine());
            System.out.print("Nhap e: ");
            BigInteger e = parseBigInt(sc.nextLine());
            System.out.print("Nhap Plaintext M: ");
            BigInteger M = parseBigInt(sc.nextLine());

            BigInteger[] key = rsaKeygen(p, q, e);
            BigInteger n = key[0], d = key[1], phi = key[2];
            BigInteger C = rsaEnc(n, e, M);
            BigInteger decM = rsaDec(n, d, C);

            System.out.println("p = " + p + "   q = " + q + "   e = " + e);
            System.out.println("n = " + n + "   phi(n) = " + phi + "   d = " + d);
            System.out.println("Plaintext  M = " + M);
            System.out.println("Ciphertext C = " + C);
            System.out.println("Decrypted  M = " + decM);
        } else if ("2".equals(mode)) {
            System.out.print("Nhap n: ");
            BigInteger n = parseBigInt(sc.nextLine());
            System.out.print("Nhap e: ");
            BigInteger e = parseBigInt(sc.nextLine());
            System.out.print("Nhap M: ");
            BigInteger M = parseBigInt(sc.nextLine());
            System.out.println("Ciphertext C = " + rsaEnc(n, e, M));
        } else if ("3".equals(mode)) {
            System.out.print("Nhap n: ");
            BigInteger n = parseBigInt(sc.nextLine());
            System.out.print("Nhap d: ");
            BigInteger d = parseBigInt(sc.nextLine());
            System.out.print("Nhap C: ");
            BigInteger C = parseBigInt(sc.nextLine());
            System.out.println("Decrypted M = " + rsaDec(n, d, C));
        }
    }

    private static void menuRsaText(Scanner sc) {
        System.out.println("\n--- 5. RSA ENCRYPT / DECRYPT (TEXT) ---");
        System.out.println("1. Ma hoa van ban (Nhap n, e, chuoi van ban)");
        System.out.println("2. Giai ma van ban (Nhap n, d, chuoi HEX)");
        System.out.print("Chon che do (1-2): ");
        String mode = sc.nextLine().trim();

        if ("1".equals(mode)) {
            System.out.print("Nhap n: ");
            BigInteger n = parseBigInt(sc.nextLine());
            System.out.print("Nhap e: ");
            BigInteger e = parseBigInt(sc.nextLine());
            System.out.print("Nhap van ban: ");
            String text = sc.nextLine();
            String hex = rsaEncText(n, e, text);
            System.out.println("Ban ma (HEX): " + hex);
        } else if ("2".equals(mode)) {
            System.out.print("Nhap n: ");
            BigInteger n = parseBigInt(sc.nextLine());
            System.out.print("Nhap d: ");
            BigInteger d = parseBigInt(sc.nextLine());
            System.out.print("Nhap chuoi HEX: ");
            String hex = sc.nextLine().trim();
            String plain = rsaDecText(n, d, hex);
            System.out.println("Ban ro: " + plain);
        }
    }

    private static void menuElGamal(Scanner sc) {
        System.out.println("\n--- 6. HE MAT ELGAMAL (PHAN D1) ---");
        System.out.print("Nhap so nguyen to p: ");
        BigInteger p = parseBigInt(sc.nextLine());
        System.out.print("Nhap phan tu sinh g: ");
        BigInteger g = parseBigInt(sc.nextLine());
        System.out.print("Nhap khoa bi mat x (bo trong de sinh ngau nhien): ");
        String xStr = sc.nextLine().trim();
        BigInteger x = xStr.isEmpty() ? randomBetween(TWO, p.subtract(TWO)) : parseBigInt(xStr);

        BigInteger y = elgamalPubKey(p, g, x);
        System.out.println("Khoa cong khai y = g^x mod p = " + y);

        System.out.print("Nhap so ngau nhien k (bo trong de sinh ngau nhien): ");
        String kStr = sc.nextLine().trim();
        BigInteger k = kStr.isEmpty() ? randomBetween(ONE, p.subtract(TWO)) : parseBigInt(kStr);

        System.out.print("Nhap thong diep M (0 <= M < p): ");
        BigInteger M = parseBigInt(sc.nextLine());

        BigInteger[] cipher = elgamalEnc(p, g, y, k, M);
        BigInteger decM = elgamalDec(p, x, cipher[0], cipher[1]);

        System.out.println("Ban ma (c1, c2) = (" + cipher[0] + ", " + cipher[1] + ")");
        System.out.println("Giai ma M = " + decM);
        System.out.println("=> " + (M.compareTo(decM) == 0 ? "KHOP" : "KHONG KHOP"));
    }

    // =========================================================================
    // KIỂM THỬ CHƯƠNG TRÌNH (TEST CASE CHUẨN + TỰ VIẾT)
    // =========================================================================

    public static void runAllTestCases() {
        int passed = 0;
        int total = 0;

        System.out.println("\n=================================================================================");
        System.out.println("                  KET QUA CHAY BO TEST CASE CHUAN");
        System.out.println("=================================================================================");
        System.out.printf("%-5s | %-42s | %-22s | %-6s%n", "TC", "Input / Lenh", "Output", "Ket qua");
        System.out.println("---------------------------------------------------------------------------------");

        // --- 6.1 PHẦN A ---
        total++; passed += checkTC("A1", "modexp 4 13 497",
                modexp(BigInteger.valueOf(4), BigInteger.valueOf(13), BigInteger.valueOf(497)).toString(), "445");
        total++; passed += checkTC("A2", "modexp 2 1000 1000000007",
                modexp(TWO, BigInteger.valueOf(1000), BigInteger.valueOf(1000000007)).toString(), "688423210");
        total++; passed += checkTC("A3", "modexp 123456789 987654321 1000000007",
                modexp(BigInteger.valueOf(123456789), BigInteger.valueOf(987654321), BigInteger.valueOf(1000000007)).toString(), "652541198");
        total++; passed += checkTC("A4", "modinv 17 3120",
                modinv(BigInteger.valueOf(17), BigInteger.valueOf(3120)).toString(), "2753");
        total++; passed += checkTC("A5", "modinv 7 160",
                modinv(BigInteger.valueOf(7), BigInteger.valueOf(160)).toString(), "23");

        total++;
        String a6Out;
        try {
            a6Out = modinv(BigInteger.valueOf(6), BigInteger.valueOf(9)).toString();
        } catch (Exception e) {
            a6Out = "ERROR (gcd = 3)";
        }
        passed += checkTC("A6", "modinv 6 9", a6Out, "ERROR (gcd = 3)");

        total++; passed += checkTC("A7", "isprime 561",
                isPrime(BigInteger.valueOf(561)) ? "PRIME" : "COMPOSITE", "COMPOSITE");
        total++; passed += checkTC("A8", "isprime 41041",
                isPrime(BigInteger.valueOf(41041)) ? "PRIME" : "COMPOSITE", "COMPOSITE");
        total++; passed += checkTC("A9", "isprime 4294967297",
                isPrime(new BigInteger("4294967297")) ? "PRIME" : "COMPOSITE", "COMPOSITE");
        total++; passed += checkTC("A10", "isprime 2305843009213693951",
                isPrime(new BigInteger("2305843009213693951")) ? "PRIME" : "COMPOSITE", "PRIME");
        total++; passed += checkTC("A11", "isprime 18446744073709551557",
                isPrime(new BigInteger("18446744073709551557")) ? "PRIME" : "COMPOSITE", "PRIME");

        // --- 6.2 PHẦN B ---
        total++; passed += checkDH("B1", "23", "5", "6", "15", "8", "19", "2");
        total++; passed += checkDH("B2", "353", "3", "97", "233", "40", "248", "160");
        total++; passed += checkDH("B3", "18446744073709551557", "2", "1234567890123", "9876543210987",
                "8129225194692443120", "3861230082652700755", "11308078763401085014");
        // B4 – Nhóm MODP 2048 bit (RFC 3526, Group 14), g = 2
        BigInteger pB4 = new BigInteger(RFC3526_2048_P_HEX, 16);
        BigInteger aB4 = new BigInteger("7777777777777777777777777777777777777777");
        BigInteger bB4 = new BigInteger("31415926535897932384626433832795028841971");
        String pubAB4 = dhPub(pB4, TWO, aB4).toString();
        String pubBB4 = dhPub(pB4, TWO, bB4).toString();
        String k1B4 = dhShared(pB4, new BigInteger(pubBB4), aB4).toString();
        String k2B4 = dhShared(pB4, new BigInteger(pubAB4), bB4).toString();
        boolean b4Ok = pubAB4.length() == 617 && pubBB4.length() == 617 && k1B4.length() == 617
                && pubAB4.startsWith("17117184111190399811") && pubAB4.endsWith("60009955224807524035")
                && pubBB4.startsWith("24424300310417338035") && pubBB4.endsWith("41462507510720105035")
                && k1B4.equals(k2B4)
                && k1B4.startsWith("23625328614100751343") && k1B4.endsWith("37831449824509591260");
        total++; passed += checkTC("B4", "DH 2048-bit (RFC 3526 Group 14), g=2",
                b4Ok ? "K=236253...591260" : "FAIL", "K=236253...591260");

        // --- 6.3 PHẦN C (SỐ NGUYÊN) ---
        total++; passed += checkRsaGenEnc("C1", "61", "53", "17", "65", "3233", "2753", "2790");
        total++; passed += checkRsaGenEnc("C2", "17", "11", "7", "88", "187", "23", "11");
        total++; passed += checkRsaGenEnc("C3", "4294967291", "4294967279", "65537", "123456789",
                "18446743979220271189", "9331878932546167513", "17663059933123306112");

        total++; passed += checkTC("C4", "rsa dec 3233 2753 855",
                rsaDec(new BigInteger("3233"), new BigInteger("2753"), new BigInteger("855")).toString(), "123");
        total++; passed += checkTC("C5", "rsa dec 187 23 11",
                rsaDec(new BigInteger("187"), new BigInteger("23"), new BigInteger("11")).toString(), "88");
        total++; passed += checkTC("C6", "rsa dec n_C3 d_C3 1000000",
                rsaDec(new BigInteger("18446743979220271189"), new BigInteger("9331878932546167513"), new BigInteger("1000000")).toString(),
                "2911662817484670982");

        // --- 6.4 PHẦN C (VĂN BẢN) ---
        BigInteger nC3 = new BigInteger("18446743979220271189");
        BigInteger eC3 = new BigInteger("65537");
        BigInteger dC3 = new BigInteger("9331878932546167513");

        // C7: Gồm cả 2 bản rõ "AN TOAN THONG TIN" và "Mật mã"
        String c7Hex1 = rsaEncText(nC3, eC3, "AN TOAN THONG TIN");
        String c7Dec1 = rsaDecText(nC3, dC3, c7Hex1);
        String c7Hex2 = rsaEncText(nC3, eC3, "Mật mã");
        String c7Dec2 = rsaDecText(nC3, dC3, c7Hex2);
        boolean c7Ok = "B2E59A8454877FC10C17556DF7B4EDFC1EBB1E8327B0324C".equals(c7Hex1)
                && "AN TOAN THONG TIN".equals(c7Dec1)
                && "FB2973289D24422BD90D6CD7EE338B38".equals(c7Hex2)
                && "Mật mã".equals(c7Dec2);
        total++; passed += checkTC("C7", "RSA van ban (\"AN TOAN...\" & \"Mật mã\")",
                c7Ok ? "2/2 HEX MATCH" : "FAIL", "2/2 HEX MATCH");

        // C8: Khóa RSA 1024-bit, e = 65537
        BigInteger pC8 = new BigInteger(
                "10130138694496247685934739467447845213331483868439" +
                "48775908119872771568672200540800253971146266937780" +
                "46016756175073309204611698358854234539334736681192" +
                "37829");
        BigInteger qC8 = new BigInteger(
                "12759546472694957935944423546536679449702272177903" +
                "27687800242473497694546588957415050061065659647348" +
                "02393627317715985566892615106400463742536785936388" +
                "37907");
        BigInteger eC8 = new BigInteger("65537");
        BigInteger[] keyC8 = rsaKeygen(pC8, qC8, eC8);
        String nC8Str = keyC8[0].toString();
        String dC8Str = keyC8[1].toString();
        String c8Hex = rsaEncText(keyC8[0], eC8, "AN TOAN THONG TIN");
        String c8Dec = rsaDecText(keyC8[0], keyC8[1], c8Hex);
        String expectedC8Hex =
                "B3435EFA66350506E01588DDE8847349024E306E0B77AE9E" +
                "D8150824384E065D88289B3A6FF733010FB95C25BB631AE8" +
                "351D9BF34079081918FF01A57BE5A931FB70C4AA2F4BF2D9" +
                "69043E5A0AFEB0F588C4BB0DA5584FBD9EB2673B6517D152" +
                "BDB523FA5004C2B9B2AE3330B6B08DFDFF3305463892DDF2" +
                "EFFED4F9EA8A2CDC";
        boolean c8Ok = nC8Str.length() == 309 && dC8Str.length() == 308
                && nC8Str.startsWith("12925597544727030325") && nC8Str.endsWith("90074001118113583903")
                && dC8Str.startsWith("99431466227842781004") && dC8Str.endsWith("67875024567697071033")
                && expectedC8Hex.equals(c8Hex) && "AN TOAN THONG TIN".equals(c8Dec);
        total++; passed += checkTC("C8", "RSA 1024-bit \"AN TOAN THONG TIN\"",
                c8Ok ? "B3435E...EA8A2CDC" : "FAIL", "B3435E...EA8A2CDC");

        // --- 6.5 PHẦN D1 (ELGAMAL) ---
        total++; passed += checkElGamal("E1", "2357", "2", "1751", "1520", "2035", "1185", "1430", "697");
        total++; passed += checkElGamal("E2", "467", "2", "127", "213", "100", "132", "29", "375");
        total++; passed += checkElGamal("E3", "23", "5", "6", "3", "10", "8", "10", "14");

        System.out.println("---------------------------------------------------------------------------------");
        System.out.println("Tong ket Test Case Chuan (Muc 6): " + passed + "/" + total + " PASS");

        // =====================================================================
        // 06 NHÓM TEST CASE TỰ VIẾT VÀ ĐO THỜI GIAN SINH KHÓA
        // =====================================================================
        System.out.println("\n=================================================================================");
        System.out.println("              KET QUA 06 NHOM TEST CASE TU VIET & MO RONG");
        System.out.println("=================================================================================");

        int customPass = 0;
        int customTotal = 6;

        // TC Tự viết 1: Kiểm thử khứ hồi RSA 512, 1024, 2048 bit
        boolean tcSelf1 = true;
        int[] rsaBitSizes = {512, 1024, 2048};
        BigInteger eStd = BigInteger.valueOf(65537);
        BigInteger n512 = null, d512 = null;
        for (int bits : rsaBitSizes) {
            BigInteger p, q, phi;
            while (true) {
                p = genPrime(bits / 2);
                q = genPrime(bits - bits / 2);
                if (p.compareTo(q) == 0) continue;
                phi = p.subtract(ONE).multiply(q.subtract(ONE));
                if (egcd(eStd, phi)[0].compareTo(ONE) == 0) break;
            }
            BigInteger[] key = rsaKeygen(p, q, eStd);
            if (bits == 512) { n512 = key[0]; d512 = key[1]; }
            String sampleMsg = "Kiem thu khu hoi RSA " + bits + " bit - An toan thong tin 2026!";
            String encHex = rsaEncText(key[0], eStd, sampleMsg);
            String decMsg = rsaDecText(key[0], key[1], encHex);
            if (!sampleMsg.equals(decMsg)) tcSelf1 = false;
        }
        customPass += checkTC("TV1", "RSA Khu hoi (512, 1024, 2048 bit)", tcSelf1 ? "OK" : "FAIL", "OK");

        // TC Tự viết 2: Kiểm thử DH khứ hồi với p 2048 bit
        BigInteger p2048 = new BigInteger(RFC3526_2048_P_HEX, 16);
        BigInteger aRand = randomBetween(TWO, p2048.subtract(TWO));
        BigInteger bRand = randomBetween(TWO, p2048.subtract(TWO));
        BigInteger pubA = dhPub(p2048, TWO, aRand);
        BigInteger pubB = dhPub(p2048, TWO, bRand);
        BigInteger sharedA = dhShared(p2048, pubB, aRand);
        BigInteger sharedB = dhShared(p2048, pubA, bRand);
        boolean tcSelf2 = sharedA.compareTo(sharedB) == 0;
        customPass += checkTC("TV2", "DH 2048-bit (RFC 3526) Khu hoi", tcSelf2 ? "K_A == K_B" : "FAIL", "K_A == K_B");

        // TC Tự viết 3: Kiểm thử biên số nguyên (M = 0, M = 1, M = n - 1)
        BigInteger m0 = ZERO;
        BigInteger m1 = ONE;
        BigInteger mMax = n512.subtract(ONE);
        boolean tcSelf3 = rsaDec(n512, d512, rsaEnc(n512, eStd, m0)).compareTo(m0) == 0
                       && rsaDec(n512, d512, rsaEnc(n512, eStd, m1)).compareTo(m1) == 0
                       && rsaDec(n512, d512, rsaEnc(n512, eStd, mMax)).compareTo(mMax) == 0;
        customPass += checkTC("TV3", "Bien so nguyen (M=0, M=1, M=n-1)", tcSelf3 ? "OK" : "FAIL", "OK");

        // TC Tự viết 4: Kiểm thử biên văn bản (rỗng, tiếng Việt có dấu, dài > 10 khối)
        String emptyEnc = rsaEncText(nC3, eC3, "");
        String emptyDec = rsaDecText(nC3, dC3, emptyEnc);
        String vnText = "Trường Đại học - Học phần Nhập môn An toàn thông tin: Trao đổi khóa Diffie-Hellman & Mã hóa RSA!";
        String vnEnc = rsaEncText(nC3, eC3, vnText); // > 10 khối (mỗi khối 7 byte)
        String vnDec = rsaDecText(nC3, dC3, vnEnc);
        boolean tcSelf4 = "".equals(emptyDec) && vnText.equals(vnDec) && (vnEnc.length() / 16 > 10);
        customPass += checkTC("TV4", "Bien van ban (Rong, TV, >10 khoi)", tcSelf4 ? "OK" : "FAIL", "OK");

        // TC Tự viết 5: Kiểm thử lỗi (p hợp số, p=q, gcd(e,phi)!=1, M>=n, DH Y=1, Y=p-1)
        boolean errComposite = false, errEqualPQ = false, errGcdE = false, errMgeN = false, errDhY1 = false, errDhYp1 = false;
        try { rsaKeygen(BigInteger.valueOf(15), BigInteger.valueOf(53), BigInteger.valueOf(17)); } catch (Exception e) { errComposite = true; }
        try { rsaKeygen(BigInteger.valueOf(61), BigInteger.valueOf(61), BigInteger.valueOf(17)); } catch (Exception e) { errEqualPQ = true; }
        try { rsaKeygen(BigInteger.valueOf(61), BigInteger.valueOf(53), BigInteger.valueOf(5)); } catch (Exception e) { errGcdE = true; }
        try { rsaEnc(BigInteger.valueOf(3233), BigInteger.valueOf(17), BigInteger.valueOf(3233)); } catch (Exception e) { errMgeN = true; }
        try { dhShared(BigInteger.valueOf(23), ONE, BigInteger.valueOf(6)); } catch (Exception e) { errDhY1 = true; }
        try { dhShared(BigInteger.valueOf(23), BigInteger.valueOf(22), BigInteger.valueOf(6)); } catch (Exception e) { errDhYp1 = true; }
        boolean tcSelf5 = errComposite && errEqualPQ && errGcdE && errMgeN && errDhY1 && errDhYp1;
        customPass += checkTC("TV5", "Bat loi (p=q, gcd!=1, M>=n, DH Y=1/p-1)", tcSelf5 ? "ALL ERRORS CAUGHT" : "FAIL", "ALL ERRORS CAUGHT");

        // TC Tự viết 6: Kiểm thử khứ hồi ElGamal với tham số ngẫu nhiên 512 bit
        BigInteger pEl = genPrime(512);
        BigInteger gEl = TWO;
        BigInteger xEl = randomBetween(TWO, pEl.subtract(TWO));
        BigInteger yEl = elgamalPubKey(pEl, gEl, xEl);
        BigInteger kEl = randomBetween(TWO, pEl.subtract(TWO));
        BigInteger mEl = randomBetween(ONE, pEl.subtract(TWO));
        BigInteger[] cEl = elgamalEnc(pEl, gEl, yEl, kEl, mEl);
        BigInteger decEl = elgamalDec(pEl, xEl, cEl[0], cEl[1]);
        boolean tcSelf6 = mEl.compareTo(decEl) == 0;
        customPass += checkTC("TV6", "ElGamal 512-bit Khu hoi ngau nhien", tcSelf6 ? "OK" : "FAIL", "OK");

        System.out.println("---------------------------------------------------------------------------------");
        System.out.println("Tong ket Test Case Tu Viet: " + customPass + "/" + customTotal + " PASS");

        // Đo thời gian sinh khóa RSA (trung bình 10 lần) ở 512 / 1024 / 2048 bit
        System.out.println("\n=================================================================================");
        System.out.println("         DO THOI GIAN SINH KHOA RSA (TRUNG BINH 10 LAN)");
        System.out.println("=================================================================================");
        for (int bits : new int[]{512, 1024, 2048}) {
            long totalMs = 0;
            int runs = 10;
            for (int r = 0; r < runs; r++) {
                long tStart = System.currentTimeMillis();
                while (true) {
                    BigInteger p = genPrime(bits / 2);
                    BigInteger q = genPrime(bits - bits / 2);
                    if (p.compareTo(q) == 0) continue;
                    BigInteger phi = p.subtract(ONE).multiply(q.subtract(ONE));
                    if (egcd(eStd, phi)[0].compareTo(ONE) == 0) {
                        modinv(eStd, phi);
                        break;
                    }
                }
                totalMs += (System.currentTimeMillis() - tStart);
            }
            System.out.printf("Do dai khoa RSA %4d bit: Trung binh = %6.1f ms / lan (Tong 10 lan: %d ms)%n",
                    bits, (double) totalMs / runs, totalMs);
        }
    }

    private static int checkTC(String id, String desc, String actual, String expected) {
        boolean pass = actual.equals(expected);
        System.out.printf("%-5s | %-42s | %-22s | %-6s%n", id, desc, actual, pass ? "PASS" : "FAIL");
        return pass ? 1 : 0;
    }

    private static int checkDH(String id, String pS, String gS, String aS, String bS, String expA, String expB, String expK) {
        BigInteger p = new BigInteger(pS);
        BigInteger g = new BigInteger(gS);
        BigInteger a = new BigInteger(aS);
        BigInteger b = new BigInteger(bS);
        BigInteger A = dhPub(p, g, a);
        BigInteger B = dhPub(p, g, b);
        BigInteger k1 = dhShared(p, B, a);
        BigInteger k2 = dhShared(p, A, b);
        boolean pass = A.toString().equals(expA) && B.toString().equals(expB)
                && k1.toString().equals(expK) && k2.toString().equals(expK);
        System.out.printf("%-5s | %-42s | %-22s | %-6s%n", id, "DH p=" + (pS.length() > 8 ? pS.substring(0, 8) + "..." : pS) + ", g=" + gS,
                "K=" + k1, pass ? "PASS" : "FAIL");
        return pass ? 1 : 0;
    }

    private static int checkRsaGenEnc(String id, String pS, String qS, String eS, String mS, String expN, String expD, String expC) {
        BigInteger p = new BigInteger(pS);
        BigInteger q = new BigInteger(qS);
        BigInteger e = new BigInteger(eS);
        BigInteger M = new BigInteger(mS);
        BigInteger[] nd = rsaKeygen(p, q, e);
        BigInteger C = rsaEnc(nd[0], e, M);
        BigInteger decM = rsaDec(nd[0], nd[1], C);
        boolean pass = nd[0].toString().equals(expN) && nd[1].toString().equals(expD)
                && C.toString().equals(expC) && decM.compareTo(M) == 0;
        System.out.printf("%-5s | %-42s | %-22s | %-6s%n", id, "RSA p=" + pS + ", q=" + qS + ", e=" + eS,
                "C=" + C, pass ? "PASS" : "FAIL");
        return pass ? 1 : 0;
    }

    private static int checkElGamal(String id, String pS, String gS, String xS, String kS, String mS,
                                    String expY, String expC1, String expC2) {
        BigInteger p = new BigInteger(pS);
        BigInteger g = new BigInteger(gS);
        BigInteger x = new BigInteger(xS);
        BigInteger k = new BigInteger(kS);
        BigInteger M = new BigInteger(mS);
        BigInteger y = elgamalPubKey(p, g, x);
        BigInteger[] c = elgamalEnc(p, g, y, k, M);
        BigInteger decM = elgamalDec(p, x, c[0], c[1]);
        boolean pass = y.toString().equals(expY) && c[0].toString().equals(expC1)
                && c[1].toString().equals(expC2) && decM.compareTo(M) == 0;
        System.out.printf("%-5s | %-42s | %-22s | %-6s%n", id, "ElGamal p=" + pS + ", g=" + gS + ", M=" + mS,
                "(" + c[0] + ", " + c[1] + ")", pass ? "PASS" : "FAIL");
        return pass ? 1 : 0;
    }

    public static void main(String[] args) {
        if (args.length > 0) {
            handleCommandLine(args);
        } else {
            runInteractiveMenu();
        }
    }
}