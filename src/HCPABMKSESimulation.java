import it.unisa.dia.gas.jpbc.Element;
import it.unisa.dia.gas.jpbc.Field;
import it.unisa.dia.gas.jpbc.Pairing;
import it.unisa.dia.gas.jpbc.PairingParameters;
import it.unisa.dia.gas.plaf.jpbc.pairing.PairingFactory;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.List;
import java.util.HashMap;
import java.util.Map;


public class HCPABMKSESimulation {
    private Pairing pairing;
    private Field G1, G2, GT, Zp;
    private Element g1, g2, alpha, b, A, X;
    private MessageDigest hash;
    private Map<String, Element> Y_map; // 存储 Y_{i,t_i} = g1^{y_{i,t_i}}

    // 初始化系统参数
    public HCPABMKSESimulation() throws NoSuchAlgorithmException {
        // 加载Type A曲线参数
        PairingParameters params = PairingFactory.getPairingParameters("a.properties");
        pairing = PairingFactory.getPairing(params);
        G1 = pairing.getG1();
        G2 = pairing.getG2();
        GT = pairing.getGT();
        Zp = pairing.getZr();
        hash = MessageDigest.getInstance("SHA-256");
        Y_map = new HashMap<>();
    }

    // Setup算法：生成系统参数和主密钥
    public class Setup {
        public void run(int n) throws NoSuchAlgorithmException {
            // 随机选择主密钥 alpha 和 b
            alpha = Zp.newRandomElement().getImmutable();
            b = Zp.newRandomElement().getImmutable();
            // 选择G1和G2的生成元
            g1 = G1.newRandomElement().getImmutable();
            g2 = G2.newRandomElement().getImmutable();
            // 计算公共参数 A = e(g1,g2)^alpha, X = g1^b
            A = pairing.pairing(g1, g2).powZn(alpha).getImmutable();
            X = g1.powZn(b).getImmutable();
            // 为每个属性生成 y_{i,t_i} 和 Y_{i,t_i}
            for (int i = 1; i <= n; i++) {
                String attr = "Attr" + i;
                Element y_i_ti = Zp.newRandomElement().getImmutable();
                Y_map.put(attr, g1.powZn(y_i_ti).getImmutable());
            }
        }
    }

    // Keygen算法：为用户生成私钥
    public class Keygen {
        private Element xu, K0;
        private List<Element> K_prime, K_double_prime;
        private List<String> attributes;

        public Keygen(List<String> S) {
            attributes = S;
            K_prime = new ArrayList<>();
            K_double_prime = new ArrayList<>();
        }

        public void run() throws NoSuchAlgorithmException {
            // 随机选择用户标识 xu 和 beta
            xu = Zp.newRandomElement().getImmutable();
            Element beta = Zp.newRandomElement().getImmutable();
            // 计算 B = A^xu (公开参数)
            Element B = A.powZn(xu).getImmutable();
            // 计算 K0 = g2^((alpha + beta)/b)
            K0 = g2.powZn(alpha.add(beta).div(b)).getImmutable();
            // 为每个属性生成 K_i' 和 K_i''
            for (String x : attributes) {
                Element lambda_i = Zp.newRandomElement().getImmutable();
                Element y_i_ti = hashStringToZp(x); 
                // K_i' = g2^(beta + y_{i,t_i} * lambda_i)
                K_prime.add(g2.powZn(beta.add(y_i_ti.mul(lambda_i))).getImmutable());
                // K_i'' = g2^(lambda_i)
                K_double_prime.add(g2.powZn(lambda_i).getImmutable());
            }
        }

        public Element getXu() { return xu; }
        public Element getK0() { return K0; }
        public List<Element> getKPrime() { return K_prime; }
        public List<Element> getKDoublePrime() { return K_double_prime; }
    }

    // CreateList算法：为用户创建用户列表
    public class CreateList {
        private Element C_U;

        public CreateList(Element xu) {
            // 随机 r
            Element r = Zp.newRandomElement().getImmutable();
            // 计算 C_U = B^r = A^(xu*r)
            Element B = A.powZn(xu).getImmutable();
            C_U = B.powZn(r).getImmutable();
        }

        public Element getC_U() { return C_U; }
    }

    // Encrypt算法：加密消息和关键字
    public class Encrypt {
        private Element C_bar, C_tilde, C_star, C, C1;
        private List<Element> Ci, C_hat_i, C_prime_i;
        private List<String> policy, keywords;

        public Encrypt(String message, List<String> P, List<String> W) throws NoSuchAlgorithmException {
            policy = P;
            keywords = W;
            Ci = new ArrayList<>();
            C_hat_i = new ArrayList<>();
            C_prime_i = new ArrayList<>();
            // 随机选择消息 M ∈ GT
            Element M = GT.newRandomElement().getImmutable();
            // 随机选择 r_i 并计算 r = Σr_i
            Element r = Zp.newZeroElement();
            List<Element> r_i_list = new ArrayList<>();
            for (int i = 0; i < P.size(); i++) {
                Element ri = Zp.newRandomElement().getImmutable();
                r_i_list.add(ri);
                r = r.add(ri);
            }
            // 随机选择 u
            Element u = Zp.newRandomElement().getImmutable();
            // 计算 C_tilde = A^r, C_bar = M * A^u
            C_tilde = A.powZn(r).getImmutable();
            C_bar = M.mul(A.powZn(u)).getImmutable();
            // 计算 C_star = g1^(b*u), C = g1^u
            C_star = g1.powZn(b.mul(u)).getImmutable();
            C = g1.powZn(u).getImmutable();
            // 计算 C1 = X^(r/(ΣH(w_j)))
            Element sum_H_wj = Zp.newZeroElement();
            for (String wj : W) {
                sum_H_wj = sum_H_wj.add(hashStringToZp(wj));
            }
            C1 = X.powZn(r.div(sum_H_wj)).getImmutable();
            // 为每个策略属性计算 Ci, C_hat_i 和 C_prime_i
            for (int i = 0; i < P.size(); i++) {
                Element ri = r_i_list.get(i);
                Ci.add(g1.powZn(ri).getImmutable());
                String Pi = P.get(i);
                if (Y_map.containsKey(Pi)) { // 假设 v_{i,t_i} ∈ P_i
                    Element Y_i_ti = Y_map.get(Pi);
                    C_hat_i.add(Y_i_ti.powZn(ri).getImmutable());
                    C_prime_i.add(Y_i_ti.powZn(u).getImmutable());
                } else { // v_{i,t_i} ∉ P_i
                    C_hat_i.add(G1.newRandomElement().getImmutable());
                    C_prime_i.add(G1.newRandomElement().getImmutable());
                }
            }
        }

        public Element getCBar() { return C_bar; }
        public Element getCTilde() { return C_tilde; }
        public Element getCStar() { return C_star; }
        public Element getC() { return C; }
        public Element getC1() { return C1; }
        public List<Element> getCi() { return Ci; }
        public List<Element> getCHatI() { return C_hat_i; }
        public List<Element> getCPrimeI() { return C_prime_i; }
    }

    // Trapdoor算法：生成查询陷门
    public class Trapdoor {
        private Element T_hat, T_0;
        private List<String> query_keywords;
        private List<Element> T_prime, T_double_prime;
        private Keygen keygen;

        public Trapdoor(Keygen keygen, List<String> W_prime) {
            this.keygen = keygen;
            query_keywords = W_prime;
            T_prime = new ArrayList<>();
            T_double_prime = new ArrayList<>();
        }

        public void run() throws NoSuchAlgorithmException {
            // 随机 s
            Element s = Zp.newRandomElement().getImmutable();
            // 计算 T_hat = xu + s
            T_hat = keygen.getXu().add(s).getImmutable();
            // 计算 T_0 = K0^(s * ΣH(w'_j))
            Element sum_H_w_prime = Zp.newZeroElement();
            for (String w_prime : query_keywords) {
                sum_H_w_prime = sum_H_w_prime.add(hashStringToZp(w_prime));
            }
            T_0 = keygen.getK0().powZn(s.mul(sum_H_w_prime)).getImmutable();
            // 计算 T'_i 和 T''_i
            for (int i = 0; i < keygen.getKPrime().size(); i++) {
                T_prime.add(keygen.getKPrime().get(i).powZn(s).getImmutable());
                T_double_prime.add(keygen.getKDoublePrime().get(i).powZn(s).getImmutable());
            }
        }

        public Element getT_hat() { return T_hat; }
        public Element getT_0() { return T_0; }
        public List<Element> getT_prime() { return T_prime; }
        public List<Element> getT_double_prime() { return T_double_prime; }
    }

    // Search算法：执行搜索和解密
    public class Search {
        private boolean matchResult;
        private Element decryptedMessage;

        public Search(Encrypt cipher, Trapdoor trapdoor, CreateList createList, Keygen keygen) {
            // Matching phase
            Element E1 = GT.newOneElement();
            Element E2 = GT.newOneElement();
            for (int i = 0; i < cipher.getCi().size(); i++) {
                E1 = E1.mul(pairing.pairing(cipher.getCi().get(i), trapdoor.getT_prime().get(i)));
                E2 = E2.mul(pairing.pairing(cipher.getCHatI().get(i), trapdoor.getT_double_prime().get(i)));
            }
            Element E = E1.div(E2);
            Element left = pairing.pairing(cipher.getC1(), trapdoor.getT_0()).mul(E.invert());
            Element right = cipher.getCTilde().powZn(trapdoor.getT_hat()).mul(createList.getC_U());
            matchResult = left.equals(right);

            // Decryption phase
            if (matchResult) {
                Element E_prime = GT.newOneElement();
                for (int i = 0; i < cipher.getCi().size(); i++) {
                    Element num = pairing.pairing(cipher.getC(), keygen.getKPrime().get(i));
                    Element den = pairing.pairing(cipher.getCPrimeI().get(i), keygen.getKDoublePrime().get(i));
                    E_prime = E_prime.mul(num.div(den));
                }
                decryptedMessage = cipher.getCBar().div(pairing.pairing(cipher.getCStar(), keygen.getK0()).div(E_prime));
            }
        }

        public boolean isMatchResult() { return matchResult; }
        public Element getDecryptedMessage() { return decryptedMessage; }
    }

    // 辅助函数：将字符串哈希到Zp
    private Element hashStringToZp(String input) throws NoSuchAlgorithmException {
        byte[] hashed = hash.digest(input.getBytes());
        return Zp.newElementFromBytes(hashed).getImmutable();
    }

    // 性能测试函数
    public void testPerformance() throws Exception {
        System.out.println("=== 性能测试结果 ===");
        // 测试属性数量变化（关键字数量固定为10）
        System.out.println("关键字数量=10，属性数量变化：");
        for (int attrNum : new int[]{10, 20, 30, 40, 50}) {
            long setupTime = 0, keygenTime = 0, encryptTime = 0, createListTime = 0, trapdoorTime = 0, searchTime = 0;
            for (int i = 0; i < 10; i++) { // 运行10次取平均
                List<String> attributes = generateAttributes(attrNum);
                List<String> keywords = generateKeywords(10);
                long start;

                // Setup
                Setup setup = new Setup();
                start = System.nanoTime();
                setup.run(attrNum);
                setupTime += System.nanoTime() - start;

                // Keygen
                Keygen keygen = new Keygen(attributes);
                start = System.nanoTime();
                keygen.run();
                keygenTime += System.nanoTime() - start;

                // Encrypt
                start = System.nanoTime();
                Encrypt encrypt = new Encrypt("TestMessage", attributes, keywords);
                encryptTime += System.nanoTime() - start;

                // CreateList
                start = System.nanoTime();
                CreateList createList = new CreateList(keygen.getXu());
                createListTime += System.nanoTime() - start;

                // Trapdoor
                Trapdoor trapdoor = new Trapdoor(keygen, keywords);
                start = System.nanoTime();
                trapdoor.run();
                trapdoorTime += System.nanoTime() - start;

                // Search
                start = System.nanoTime();
                Search search = new Search(encrypt, trapdoor, createList, keygen);
                searchTime += System.nanoTime() - start;
            }
            System.out.printf("属性数量=%d: Setup=%.2fms, Keygen=%.2fms, Encrypt=%.2fms, CreateList=%.2fms, Trapdoor=%.2fms, Search=%.2fms%n",
                    attrNum, setupTime / 1e6 / 10, keygenTime / 1e6 / 10, encryptTime / 1e6 / 10,
                    createListTime / 1e6 / 10, trapdoorTime / 1e6 / 10, searchTime / 1e6 / 10);
        }

        // 测试关键字数量变化（属性数量固定为10）
        System.out.println("\n属性数量=10，关键字数量变化：");
        for (int kwNum : new int[]{10, 20, 30, 40, 50}) {
            long setupTime = 0, keygenTime = 0, encryptTime = 0, createListTime = 0, trapdoorTime = 0, searchTime = 0;
            for (int i = 0; i < 10; i++) { // 运行10次取平均
                List<String> attributes = generateAttributes(10);
                List<String> keywords = generateKeywords(kwNum);
                long start;

                // Setup
                Setup setup = new Setup();
                start = System.nanoTime();
                setup.run(10);
                setupTime += System.nanoTime() - start;

                // Keygen
                Keygen keygen = new Keygen(attributes);
                start = System.nanoTime();
                keygen.run();
                keygenTime += System.nanoTime() - start;

                // Encrypt
                start = System.nanoTime();
                Encrypt encrypt = new Encrypt("TestMessage", attributes, keywords);
                encryptTime += System.nanoTime() - start;

                // CreateList
                start = System.nanoTime();
                CreateList createList = new CreateList(keygen.getXu());
                createListTime += System.nanoTime() - start;

                // Trapdoor
                Trapdoor trapdoor = new Trapdoor(keygen, keywords);
                start = System.nanoTime();
                trapdoor.run();
                trapdoorTime += System.nanoTime() - start;

                // Search
                start = System.nanoTime();
                Search search = new Search(encrypt, trapdoor, createList, keygen);
                searchTime += System.nanoTime() - start;
            }
            System.out.printf("关键字数量=%d: Setup=%.2fms, Keygen=%.2fms, Encrypt=%.2fms, CreateList=%.2fms, Trapdoor=%.2fms, Search=%.2fms%n",
                    kwNum, setupTime / 1e6 / 10, keygenTime / 1e6 / 10, encryptTime / 1e6 / 10,
                    createListTime / 1e6 / 10, trapdoorTime / 1e6 / 10, searchTime / 1e6 / 10);
        }
    }

    // 生成随机属性列表
    private List<String> generateAttributes(int n) {
        List<String> attributes = new ArrayList<>();
        for (int i = 1; i <= n; i++) {
            attributes.add("Attr" + i);
        }
        return attributes;
    }

    // 生成随机关键字列表
    private List<String> generateKeywords(int m) {
        List<String> keywords = new ArrayList<>();
        for (int i = 1; i <= m; i++) {
            keywords.add("Keyword" + i);
        }
        return keywords;
    }

    // 主函数
    public static void main(String[] args) {
        try {
            HCPABMKSESimulation sim = new HCPABMKSESimulation();
            sim.testPerformance();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
