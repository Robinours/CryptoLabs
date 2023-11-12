# BOUIMEDJ Sylia 22011983
# MVUKULU Robin 21813788
# MAZOUAK Ayoub 21913331


from random import randint
from hashlib import sha256, sha384

class Groupe:
    def __init__(self, p, e, N, l, A=None, B=None):
        self.p = p
        self.e = e
        self.N = N
        self.l = l
        self.A = A
        self.B = B

    def loi(self, g1, g2):
        if self.l == 'Zp-additif':
            return (g1 + g2) % self.p

        elif self.l == 'Zp-multiplicatif':
            return (g1 * g2) % self.p

        elif self.l == 'courbe-P-256':
            Zp = Groupe(self.p,1,self.p-1,'Zp-multiplicatif',None,None)
            if g1 == self.e:#1
                return g2
            if g2 == self.e:#1
                return g1
            if (g1[0] == g2[0]) and (g1[1] != g2[1]):#2
                return self.e
            if ((g1[0] == g2[0]) == 0) and ((g1[1] == g2[1])): #3
                return  self.e
            if (g1[0] == g2[0]) and ((g1[1] == g2[1]) != 0): #4
                l = ((3 * g1[0] ** 2  + self.A)*Zp.squareAndMultiply(2*g2[1],-1))% self.p
                x = (l ** 2 - 2*(g1[0])) % self.p
                y = (l*(g1[0]-x)-g1[1]) % self.p
                return (x,y)
            if g1[0] != g2[0]:#5
                l = ((g2[1] - g1[1]) * Zp.squareAndMultiply(g2[0] - g1[0],-1))% self.p
                x = (l ** 2 - g1[0] - g2[0])%self.p
                y = (l*(g1[0]-x)-g1[1])%self.p
                return  (x,y)

        elif self.l == 'Curve25519':
            Zp = Groupe(self.p,1,self.p-1,'Zp-multiplicatif',None,None)
            if g1 == self.e:
                return g2
            if g2 == self.e:
                return g1
            x1, y1 = g1
            x2, y2 = g2
            if x1 == x2 and y1 != y2:
                return self.e
            if x1 == x2:
                m = (3*x1**2 + 2*self.A*x1 + 1) * Zp.squareAndMultiply(2*y1,-1)%self.p
            else:
                m = (y2 - y1) * Zp.squareAndMultiply(x2 - x1,-1)%self.p
            x3 = (m**2 - self.A - x1 - x2) %self.p
            y3 = (m*(x1 - x3) - y1) % self.p
            return (x3, y3)

        else:
                raise Exception('Loi de groupe non reconnue.')

    def squareAndMultiply(self, g, k):
        if k == 0:
            return self.e
        elif k == -1:
            return self.squareAndMultiply(g,self.N-1)
        result = self.e
        while k > 0:
            if k % 2 == 1:
                result = self.loi(result, g)
            g = self.loi(g, g)
            k //= 2
        return result

    def MontgomeryLadder(self, g, k):
        if k == 0:
            return self.e
        elif k == -1:
            return self.MontgomeryLadder(g,self.N-1)
        h0 = self.e
        h1 = g
        t = k.bit_length() - 1
        for i in range(t,-1,-1):
            if (k >> i) & 1 == 0:
                h1 = self.loi(h0, h1)
                h0 = self.loi(h0, h0)
            else:
                h0 = self.loi(h1, h0)
                h1 = self.loi(h1, h1)
        return h0


class Crypto(Groupe):
    def __init__(self, p, e, N, l, g, A=None, B=None):
        super().__init__(p, e, N, l, A, B)
        self.g = g

    def testDiffieHellman(self):
        a = randint(0, self.N-1)
        b = randint(0, self.N-1)
        A = self.squareAndMultiply(self.g, a)
        B = self.MontgomeryLadder(self.g, b)
        K1 = self.squareAndMultiply(B, a)
        K2 = self.MontgomeryLadder(A, b)
        return K1 == K2

    def DiffieHellman(self, a, b, A, B, K):
        if (A == self.squareAndMultiply(self.g, a)):
            if (B == self.squareAndMultiply(self.g, b)):
                x = self.squareAndMultiply(A, b)
                y = self.squareAndMultiply(B, a)
                if ((K == x ) and (K == y )):
                    return True
        return False

    def reverse_bytes_25519(self, b):
        return sum(((b >> 8 * (31 - i)) & 0xff) << (8*i) for i in range(32))

    def ecdsa_sign(self, m, priv_key):
        m = int(sha256(m).hexdigest(), 16) #Hash
        k = randint(1, self.N - 1)
        P = self.squareAndMultiply(self.g, k)
        t = P[0] % self.N
        k_inverse = pow(k,-1,self.N)
        s = (k_inverse * (m + priv_key * t)) % self.N
        return (t, s)

    def ecdsa_verif(self, m, pub_key, sign):
        t, s = sign
        if t < 1 or t > self.N-1 or s < 1 or s > self.N-1:
            return False
        s_inv = pow(s,-1,self.N)
        m = int(sha256(m).hexdigest(), 16)
        m_s = m * s_inv
        t_s = t * s_inv
        R1 = self.squareAndMultiply(self.g, m_s)
        R2 = self.squareAndMultiply(pub_key,t_s)
        R = self.loi(R1, R2)
        if R[0] % self.N == t:
            return True
        return False


def test_lab1():

    print("Test Lab n°1:")

    # Vérification avec p = 23, g = 5 et k = 7 Output = 12
    groupe = Groupe(23, 0, 23, 'Zp-additif')
    print("Test groupe additif avec p = 23, g = 5, k = 7: ", groupe.squareAndMultiply(5, 7))

    # Vérification avec p = 23, g = 5, k = -1 Output = 18
    groupe = Groupe(23, 0, 23, 'Zp-additif')
    print("Test groupe additif avec p = 23, g = 5, k = -1: ",groupe.squareAndMultiply(5, -1))

    # testDiffieHellman dans Z23 avec g = 5 Output = True
    crypto = Crypto(23, 0, 23, 'Zp-additif', 5)
    print("TestDiffieHellman dans Z23 avec g = 5: ",crypto.testDiffieHellman())

    # Vérification DiffieHellman dans Z23 avec g = 5, a = 5, b = 6 Output = True
    a = 5
    b = 6
    A = crypto.squareAndMultiply(5, a)
    B = crypto.squareAndMultiply(5, b)
    K = crypto.squareAndMultiply(A, b)
    result = crypto.DiffieHellman(a, b, A, B, K)
    print("Resultat de la méthode de DiffieHellman: ", result)
    print("\n")

def test_lab2():

    print("Test Lab n°2:")

    # Test avec squareAndMultiply p = 23, g = 5, k = 7 Output = 17
    groupe = Groupe(23, 1, 22, 'Zp-multiplicatif')
    print("Test avec squareAndMultiply p = 23, g = 5, k = 7: ",groupe.squareAndMultiply(5, 7))

    # Test avec MontgomeryLadder p = 23, g = 5, k = 7 Output = 17
    groupe = Groupe(23, 1, 22, 'Zp-multiplicatif')
    print("Test avec MontgomeryLadder p = 23, g = 5, k = 7: ", groupe.MontgomeryLadder(5, 7))

    # Test de l'inverse modulaire 5mod23 Output = 14
    groupe = Groupe(23, 1, 22, 'Zp-multiplicatif')
    print("Test de l'inverse modulaire 5mod23: ", groupe.squareAndMultiply(5,-1))

    # Récupération des paramètres p, g et N
    f = open("dh_param.der", 'rb')
    dh_param = f.read()
    f.close()
    data = bytearray(dh_param)
    p = int.from_bytes(data[8:265], byteorder="big")
    g = int.from_bytes(data[269:525], byteorder="big")
    N = int.from_bytes(data[527:], byteorder="big")

    #Test des paramètres récupérés avec testDiffieHellman Output = True
    crypto = Crypto(p, 1, N-1, 'Zp-multiplicatif', g)
    print("TestDiffieHellman avec les paramètres p, g et N récupérés: ", crypto.testDiffieHellman())

    # Récupération des clés générées
    f = open("cle_public_alice.txt", 'r')
    public_key_alice = f.read()
    A = int("0x" + public_key_alice,16)
    f.close()

    f = open("cle_prive_alice.txt", 'r')
    prive_key_alice = f.read()
    a = int("0x" + prive_key_alice,16)
    f.close()

    f = open("cle_public_bob.txt", 'r')
    public_key_bob = f.read()
    B = int("0x" + public_key_bob,16)
    f.close()

    f = open("cle_private_bob.txt", 'r')
    prive_key_bob = f.read()
    b = int("0x" + prive_key_bob,16)
    f.close()

    f = open('dhkey1.bin','rb')
    k1 = f.read()
    k1 = int.from_bytes(k1, byteorder='big')
    f.close()

    # Vérification DiffieHellman avec les paramètres récupérés Output = True
    result = crypto.DiffieHellman(a, b, A, B, k1)
    print("Resultat de la méthode de DiffieHellman avec les clés générées: ", result)
    print("\n")

def test_lab3():

    print("Test Lab n°3:")

    # Paramètres de la courbe P-256
    p = 2**256 - 2**224 + 2**192 + 2**96 - 1
    A = -3
    B = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
    N = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
    Gx = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
    Gy = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
    G = [Gx,Gy]
    e = [0,0]

    #Test des paramètres de la courbe P-256 avec testDiffieHellman Output = True
    groupe = Crypto(p, e, N, 'courbe-P-256', G, A, B)
    print("TestDiffieHellman avec les paramètres de la courbe P-256: ", groupe.testDiffieHellman())


    #Récupération des données
    f = open("cle_public_alice2.txt", 'r')
    public_key_alice = f.read()
    ecdhA = int("0x" + public_key_alice,16)
    f.close()

    f = open("cle_prive_alice2.txt", 'r')
    prive_key_alice = f.read()
    ecdha = int("0x" + prive_key_alice,16)
    f.close()

    f = open("cle_public_bob2.txt", 'r')
    public_key_bob = f.read()
    ecdhB = int("0x" + public_key_bob,16)
    f.close()

    f = open("cle_prive_bob2.txt", 'r')
    prive_key_bob = f.read()
    ecdhb = int("0x" + prive_key_bob,16)
    f.close()

    # Extraction des coordonnées x et y des clés publiques d'Alice et de Bob
    public_x_alice = int(public_key_alice[2:66], 16)
    public_y_alice = int(public_key_alice[66:], 16)
    public_x_bob = int(public_key_bob[2:66], 16)
    public_y_bob = int(public_key_bob[66:], 16)


    # Vérification que la clé publique d'Alice est un point sur la courbe elliptique courbe P-256
    if (public_y_alice**2) % p == (public_x_alice**3 + A*public_x_alice + B) % p:
        print("La clé publique d'Alice est un point sur la courbe elliptique")
    else:
        print("La clé publique d'Alice n'est pas un point sur la courbe elliptique")

    # Vérification que la clé d'Alice est égale à la multiplication de la clé privée et de G avec squareAndMultiply
    xA = groupe.squareAndMultiply(G,ecdha)
    xB = groupe.squareAndMultiply(G,ecdhb)
    k_partage = groupe.squareAndMultiply(xA,ecdhb)

    if xA == (public_x_alice, public_y_alice):
        print("La clé calculée correspond bien à la multiplication de la clé privée et de G")
    else:
        print("La clé calculée ne correspond pas à la multiplication de la clé privée et de G")

    # Vérification que la méthode squareAndMultiply permet de retrouver l'inverse d'un point.
    InvxA = (public_x_alice,-public_y_alice %p) #L'inverse du point x
    SqxA = groupe.squareAndMultiply(xA,-1)

    if ((SqxA[0] == InvxA[0]) and (SqxA[1] == InvxA[1])):
        print("SquareAndMultiply permet de retrouver l'inverse d'un point de la courbe P-256")
    else:
        print("SquareAndMultiply ne permet pas de retrouver l'inverse d'un point de la courbe P-256")

    # Appeler DiffieHellman avec les clés récupérés
    f = open('ecdhkey1.bin','rb')
    ecdhk1 = f.read()
    ecdhk1 = int.from_bytes(ecdhk1, byteorder='big')

    result = groupe.DiffieHellman(ecdha, ecdhb,xA, xB, k_partage)
    print("Resultat de la méthode de DiffieHellman avec les clés ecdh générées: ", result)

    #Lecture du fichier Labs.pdf
    f = open('Labs.pdf', 'rb')
    labs_pdf = f.read()
    f.close()

    #Signature du fichier Labs.pdf
    signature = groupe.ecdsa_sign(labs_pdf,ecdha)

    #Vérification de la signature dans le cas où l'on signe avec la methode ecdsa_sign
    print("Resultat de la vérification de la signature signé par ecdsa_sign: ",groupe.ecdsa_verif(labs_pdf, xA, signature))

    # Récupération de la signature générée avec OpenSSL cette fois-ci
    # Générer: openssl dgst -sha256 -sign ecdhkeyAlice.pem -out signature Labs.pdf
    # On récupère les valeurs des paramètres x et y à patir du fichier signature générer par OpenSSL
    # Récupération: openssl asn1parse -inform DER -in signature -i
    par_x = int("851AE0E6C3245897016D43710C3D53DEBC9C6998DBFEC9A336938DF6E771E522",16)
    par_y = int("5612E26EF3BC3834FAE089EBC0E4170C4193039DD7C91AB7C6CDA35F00D5DD32",16)
    signature = (par_x, par_y)

    #Vérification de la signature dans le cas où l'on signe avec la commande OpenSSL
    print("Resultat de la vérification de la signature signée par la commande OpenSSL: ", groupe.ecdsa_verif(labs_pdf, xA, signature))
    print("\n")

def test_lab4():

    print("Test Lab n°4:")

    # Paramètres de la courbe Curve25519 et testDiffieHellman
    p = 2**255 - 19
    A = 486662
    N = 2**252 + 0x14def9dea2f79cd65812631a5cf5d3ed
    Gx = 9
    Gy = 0x20ae19a1b8a086b4e01edd2c7748d14c923d4d7e6d7c61b229e9c5a27eced3d9
    G = (Gx,Gy)
    e = [0,1]
    groupe = Crypto(p, e, N, 'Curve25519', G, A)
    print("TestDiffieHellman avec les paramètres de la courbe 25519: ",groupe.testDiffieHellman())

    #Récupération des données
    f = open("cle_public_alice3.txt", 'r')
    public_key_alice = f.read()
    public_key_alice = int("0x" + public_key_alice, 16)
    f.close()

    f = open("cle_prive_alice3.txt", 'r')
    prive_key_alice = f.read()
    prive_key_alice = int("0x" + prive_key_alice, 16)
    f.close()

    f = open("cle_public_bob3.txt", 'r')
    public_key_bob = f.read()
    public_key_bob = int("0x" + public_key_bob, 16)
    f.close()

    f = open("cle_prive_bob3.txt", 'r')
    prive_key_bob = f.read()
    prive_key_bob = int("0x" + prive_key_bob, 16)
    f.close()

    # Vérification que la clé publique d'Alice est un point sur la courbe Curve25519
    s = groupe.reverse_bytes_25519(prive_key_alice) & ((1 << 255)-8) | (1 << 254)
    Q_alice = groupe.squareAndMultiply(G, s)
    x,y = Q_alice
    y_square = (y ** 2) % p
    formule = (x ** 3 + A * x ** 2 + x) % p

    if y_square == formule :
        print("La clé publique d'Alice est un point sur la courbe Curve25519")
    else:
        print("La clé publique d'Alice n'est pas un point sur la courbe Curve25519")


    # Vérification que la clé d'Alice est égale à la multiplication de la clé privée et de G avec squareAndMultiply

    ALICE = groupe.reverse_bytes_25519(public_key_alice) & ((1 >>255)-1) | (1 >> 254)
    if Q_alice[0] == ALICE :
        print("La clé calculée correspond bien à la multiplication de la clé privée et de G")
    else:
        print("La clé calculée ne correspond pas à la multiplication de la clé privée et de G")


    # Vérification que la méthode squareAndMultiply permet de retrouver l'inverse d'un point.
    InvxA = (x,-y %p) #L'inverse du point x
    SqxA = groupe.squareAndMultiply(Q_alice,-1)

    if ((SqxA[0] == InvxA[0]) and (SqxA[1] == InvxA[1])):
        print("SquareAndMultiply permet de retrouver l'inverse d'un point de la courbe 25519")
    else:
        print("SquareAndMultiply ne permet pas de retrouver l'inverse d'un point de la courbe 25519")


    # Appeller DiffieHellman avec les clés récupérés
    b = groupe.reverse_bytes_25519(public_key_bob) & ((1 << 255)-8) | (1 << 254)
    Q_bob = groupe.squareAndMultiply(G,b)
    k_partage = groupe.squareAndMultiply(Q_alice,b)

    result = groupe.DiffieHellman(s, b, Q_alice, Q_bob, k_partage)
    print("Resultat de la méthode de DiffieHellman avec les clés x25519 générées: ", result)
    print("\n")

def test_lab5():

    print("Test Lab n°5:")

    #Pour le site Unicaen.fr

    # Exposant publique
    e = 65537

    # Récupération des données
    f = open("SignatureRSA.txt", 'r')
    s = f.read()
    s = int("0x" + s, 16)
    f.close()

    f = open("Modulo.txt", 'r')
    M = f.read()
    M = int("0x" + M, 16)
    f.close()

    f = open("./unicaen-fr.der", 'rb')
    cert = f.read()
    f.close()

    #openssl s_client -connect unicaen.fr:443 -showcerts </dev/null 2>/dev/null | openssl x509 -outform PEM > unicaen-fr_certification.pem
    f = open("./unicaen-fr_certification.der", 'rb')
    certificat = f.read()
    f.close()

    # Extraire l'empreinte du certificat
    msg_hash = "0x" + sha256(cert[4:0x5c5]).hexdigest()

    # Extraire la clé publique de vérification à partir du certificat de l'autorité de certification
    N = int.from_bytes(certificat[0x192:0x292], byteorder="big")



    # Calcul de l'empreinte à partir de la signature du certificat, de l'exposant publique et de la clé publique de vérification du certificat à l'autorité de certification
    h = pow(s, e, N)

    # Ajout du mask pour enlever uniquement le préfixe
    h = h & ((1 << 256) - 1)

    #Vérification que l'on retrouve bien la même empreinte

    if(hex(h) == msg_hash):
        print("La signature du certificat du site web unicaen.fr est valide")
    else:
        print("La signature du certificat du site web unicaen.fr est invalide")

    #Pour le site Wikipedia.org

    # Exposant publique trouvable dans pub Subject Public Key Info: Public Key Algorithm: id-ecPublicKey Public-Key: (256 bit) pub:
    # Comme c'est une clé publique ECDSA l'exposant publique est la coordonnée X de (0x04 X:1ba73b45d7d1948351b92073aef3fb77af348815ae9edb, Y:e6a29d98d5d7d3de1165dd7b1fb40ee534c0fba27def07cdfa64ae45522ddd4c4338a169f4606cac09)
    e_wiki = 0x1ba73b45d7d1948351b92073aef3fb77af348815ae9edb

    #Signature du certificat = Signature Algorithm: ecdsa_with_SHA384
    s_wiki = 0x3064023019ffd1308cfa3af1a070e494aec920f1d5582b68130a192b571509d0dddd8b4b9607b37c8ea7e1990fe86319a2a97865023076bb188c8ddcf624714262d8b2e901553a2e94476e2bf7bda89802dbc92f6c17e0d5e8c068a52459929f5ed2aeed7719

    # Récupération des données
    f = open("./wikipedia-org.der", 'rb')
    cert_wiki = f.read()
    f.close()

    f = open("./wikipedia-org_certification.der", 'rb')
    certificat_wiki = f.read()
    f.close()

    # Extraction de l'empreinte SHA-384 sans la signature
    msg_hash_wiki = "0x" + sha384(cert_wiki[4:0x7e4]).hexdigest()

    #openssl s_client -showcerts -connect wikipedia.org:443 </dev/null 2>/dev/null|openssl x509 -outform PEM > wikipedia-org_certification.pem
    # Extraire N à partir du modulus: Taille modulo = 101 octets
    N_wiki = int.from_bytes(certificat_wiki[0x134:0x235], byteorder="big")

    # Calcul de l'empreinte à partir de la signature du certificat, de l'exposant publique et de la clé publique de vérification du certificat à l'autorité de certification
    h_wiki = pow(int(s_wiki), int(e_wiki), N_wiki)

    #Vérification que l'on retrouve bien la même empreinte
    if(hex(h_wiki) == msg_hash_wiki):
        print("La signature du certificat du site web wikipedia.org est valide")
    else:
        print("h_wiki", hex(h_wiki))
        print("msg_hash_wiki",msg_hash_wiki)
        print("La signature du certificat du site web wikipedia.org est invalide")

if __name__ == "__main__":
    test_lab1()
    test_lab2()
    test_lab3()
    test_lab4()
    test_lab5()
