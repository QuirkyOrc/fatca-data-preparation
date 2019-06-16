import java.io.*;
import java.security.GeneralSecurityException;
import java.security.InvalidKeyException;
import java.security.Key;
import java.security.KeyStore;
import java.security.NoSuchAlgorithmException;
import java.security.PrivateKey;
import java.security.PublicKey;
import java.security.SecureRandom;
import java.security.cert.Certificate;
import java.security.cert.X509Certificate;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.TimeZone;
import java.util.zip.Deflater;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

import javax.crypto.Cipher;
import javax.crypto.CipherInputStream;
import javax.crypto.CipherOutputStream;
import javax.crypto.KeyGenerator;
import javax.crypto.NoSuchPaddingException;
import javax.crypto.SecretKey;
import javax.crypto.spec.SecretKeySpec;
import javax.xml.bind.DatatypeConverter;
import javax.xml.crypto.AlgorithmMethod;
import javax.xml.crypto.KeySelector;
import javax.xml.crypto.KeySelectorException;
import javax.xml.crypto.KeySelectorResult;
import javax.xml.crypto.XMLCryptoContext;
import javax.xml.crypto.XMLStructure;
import javax.xml.crypto.dom.DOMStructure;
import javax.xml.crypto.dsig.CanonicalizationMethod;
import javax.xml.crypto.dsig.DigestMethod;
import javax.xml.crypto.dsig.Reference;
import javax.xml.crypto.dsig.SignatureMethod;
import javax.xml.crypto.dsig.SignedInfo;
import javax.xml.crypto.dsig.XMLObject;
import javax.xml.crypto.dsig.XMLSignature;
import javax.xml.crypto.dsig.XMLSignatureFactory;
import javax.xml.crypto.dsig.dom.DOMSignContext;
import javax.xml.crypto.dsig.dom.DOMValidateContext;
import javax.xml.crypto.dsig.keyinfo.KeyInfo;
import javax.xml.crypto.dsig.keyinfo.KeyInfoFactory;
import javax.xml.crypto.dsig.keyinfo.X509Data;
import javax.xml.crypto.dsig.spec.C14NMethodParameterSpec;
import javax.xml.crypto.dsig.spec.TransformParameterSpec;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

public class FATCADataPreparation {

	public static final String SIGNATURE_ALGORITHM = "http://www.w3.org/2001/04/xmldsig-more#rsa-sha256";
	public static final int AES_KEY_SIZE = 256;
	public static final int BUFFER_SIZE = 2048;

	public static void main(String[] args) throws Exception {

		// TEST parameters
		String inputGIIN = "000000.00000.TA.124";
		String inputReciver = "000000.00000.TA.840";

		String senderKeyAlias = "myp12key";
		String receiverKeyAlias = "myp12key";
		String senderKeyStore = "Keystore/mykeystore.p12";
		String senderKeyStorePassword = "password";
		String receiverKeyStore = "Keystore/mykeystore.p12";
		String receiverKeyStorePassword = "password";
		String receiverPassword = "password";
		String signedObjectTag = "FATCA";
		String workingDirectory = "/Users/Bowen/Documents/FATCADataPreparation";
		// The path to store all final files which will be compressed and
		// submitted
		String finalOutputFolder = "/Users/Bowen/Documents/FATCADataPreparation/Archive";
		// The unarchive path
		String unarchiveFolder = "/Users/Bowen/Documents/FATCADataPreparation/Unarchive";

		// Change ignoreLineBreaks system parameter value to true
		ignoreXMLLineBreaks();

		// Create new date format and UTC time zone to satisfy final compressed
		// file name requirement
		DateFormat dateFormat = new SimpleDateFormat("yyyyMMdd'T'HHmmssSSS'Z'");
		TimeZone utc = TimeZone.getTimeZone("UTC");

		// Get current date time and compose it to UTC format
		Date date = new Date();
		dateFormat.setTimeZone(utc);
		String UTCTime = dateFormat.format(date);

		String signedPayloadPath = workingDirectory + File.separator
				+ inputGIIN + "_Payload.xml";
		String senderKeyStorePath = workingDirectory + File.separator
				+ senderKeyStore;
		String FATCAXMLPath = workingDirectory + File.separator + inputGIIN
				+ ".xml";
		createDigitalSignature(FATCAXMLPath, signedPayloadPath,
				senderKeyStorePath, senderKeyStorePassword,
				senderKeyStorePassword, senderKeyAlias, signedObjectTag);

		String compressedPayloadPath = workingDirectory + File.separator
				+ inputGIIN + "_Payload.zip";
		archive(signedPayloadPath, workingDirectory, compressedPayloadPath);

		SecretKey aesKey = createAESKey();
		String encryptedPayloadPath = finalOutputFolder + File.separator
				+ inputGIIN + "_Payload";
		encryptWithAES(compressedPayloadPath, encryptedPayloadPath, aesKey);

		String encryptedKeyPath = finalOutputFolder + File.separator
				+ inputReciver + "_Key";
		String receiverKeyStorePath = workingDirectory + File.separator
				+ receiverKeyStore;
		encyrptWithPublicKey(encryptedKeyPath, receiverKeyStorePath,
				receiverKeyStorePassword, receiverKeyAlias, aesKey.getEncoded());

		// Create a new ArrayList and add in all files need to be compressed,
		// then archive all of them
		List<String> filePathList = new ArrayList<String>();
		filePathList = generateFileList(finalOutputFolder, finalOutputFolder,
				filePathList);
		String finalOutputPath = workingDirectory + File.separator + UTCTime
				+ "_" + inputGIIN + ".zip";
		archive(filePathList, finalOutputFolder, finalOutputPath);

		// Reverse steps begin with unarchive
		HashMap<String, String> unarchivedFiles = (HashMap<String, String>) unarchive(finalOutputPath, unarchiveFolder);
		String unarchiveEncryptedKeyPath =  unarchivedFiles.get("key");
		SecretKey decryptedAESKey = decryptWithPrivateKey(
				unarchiveEncryptedKeyPath, receiverKeyStorePath,
				receiverKeyStorePassword, receiverPassword, receiverKeyAlias);

		String encryptedAESKeyPath = unarchivedFiles.get("payload");
		String decryptedPayloadPath = unarchiveFolder + File.separator + inputGIIN + "_Payload.zip";
		decryptWithAESKey(decryptedAESKey, encryptedAESKeyPath,
				decryptedPayloadPath);
		
		unarchivedFiles = (HashMap<String, String>) unarchive(decryptedPayloadPath, unarchiveFolder);
		String unarchivedPayloadPath = unarchivedFiles.get("xml");
		
		boolean validationResult = validateXmlSignature(unarchivedPayloadPath);
	   	 
	   	if(validationResult == true) {
    	    System.out.println("Signature passed core validation");
    	}

	}

	// Change ignoreLineBreaks system parameter value to true
	// to extend 76 maximum characters length in one line
	public static void ignoreXMLLineBreaks() {
		Properties props = System.getProperties();
		props.setProperty("com.sun.org.apache.xml.internal.security.ignoreLineBreaks", "true");
	}

	// Step 1, Digital signature and enveloping FACTA XML file
	public static void createDigitalSignature(String inputPath,
			String outputPath, String keyStorePath, String keyStorePassword,
			String keyPassword, String keyAlias, String signedObjectTag)
			throws Exception {

		// First, create the DOM XMLSignatureFactory that will be used to
		// generate the XMLSignature
		XMLSignatureFactory fac = XMLSignatureFactory.getInstance("DOM");

		// Next, create a Reference to a same-document URI that is an Object
		// element and specify the SHA256 digest algorithm
		Reference ref = fac.newReference("#" + signedObjectTag, fac.newDigestMethod(DigestMethod.SHA256, null), 
				Collections.singletonList(fac.newTransform(CanonicalizationMethod.EXCLUSIVE,
						(TransformParameterSpec) null)), null, null);

		// Create the XML Object element and insert FACTCA XML file into it
		DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
		dbf.setNamespaceAware(true);
		DocumentBuilder db = dbf.newDocumentBuilder();
		Document outputXMLDoc = db.newDocument();

		// Read in FATCA XML file and get the root node
		Document inputXMLDoc = db.parse(new File(inputPath));
		inputXMLDoc.getDocumentElement().normalize();
		Node rootNode = inputXMLDoc.getDocumentElement();
		XMLStructure content = new DOMStructure(rootNode);
		XMLObject obj = fac.newXMLObject(Collections.singletonList(content),
				signedObjectTag, null, null);

		// Create the SignedInfo
		SignedInfo si = fac.newSignedInfo(fac.newCanonicalizationMethod(CanonicalizationMethod.EXCLUSIVE,
				(C14NMethodParameterSpec) null), fac.newSignatureMethod(
				SIGNATURE_ALGORITHM, null), Collections.singletonList(ref));

		// Load the KeyStore and get the signing key and certificate.
		KeyStore ks = KeyStore.getInstance("PKCS12");
		ks.load(new FileInputStream(keyStorePath),
				keyStorePassword.toCharArray());
		KeyStore.PrivateKeyEntry keyEntry = (KeyStore.PrivateKeyEntry) ks.getEntry(keyAlias,
						new KeyStore.PasswordProtection(keyPassword.toCharArray()));
		X509Certificate cert = (X509Certificate) keyEntry.getCertificate();

		// Create the KeyInfo containing the X509Data.
		KeyInfoFactory kif = fac.getKeyInfoFactory();
		List x509Content = new ArrayList();
		x509Content.add(cert.getSubjectX500Principal().getName());
		x509Content.add(cert);
		X509Data xd = kif.newX509Data(x509Content);
		KeyInfo ki = kif.newKeyInfo(Collections.singletonList(xd));

		// Create the XMLSignature (but don't sign it yet)
		XMLSignature signature = fac.newXMLSignature(si, ki,
				Collections.singletonList(obj), null, null);

		// Create a DOMSignContext and specify the PrivateKey for signing
		// and the document location of the XMLSignature
		DOMSignContext dsc = new DOMSignContext(keyEntry.getPrivateKey(), outputXMLDoc);

		// Lastly, generate the enveloping signature using the PrivateKey
		signature.sign(dsc);

		// output the resulting document
		TransformerFactory tf = TransformerFactory.newInstance();
		Transformer trans = tf.newTransformer();
		trans.transform(new DOMSource(outputXMLDoc), new StreamResult(new File(
				outputPath)));
	}

	// Generates one time AES 256 key to encrypt compressed file and will be
	// used to encrypt by receiver's public key
	// Since Java support AES 128 as default, to allow 256 bits, user need to
	// replace
	// two new jar files in all dir {java.home}/jre/lib/security
	// with US_export_policy.jara and local_policy.jar
	public static SecretKey createAESKey() throws NoSuchAlgorithmException {
		SecureRandom secureRandom = new SecureRandom();
		KeyGenerator kgen = KeyGenerator.getInstance("AES");
		kgen.init(AES_KEY_SIZE, secureRandom);
		SecretKey secKey = kgen.generateKey();
		
		if (secKey != null) {
			System.out.println("AES key is: " + DatatypeConverter.printBase64Binary(secKey.getEncoded()));
		}
		
		return secKey;
	}

	// Step 3, Encrypts and then copies the contents of a given file with AES
	// 256 key
	public static void encryptWithAES(String inputPath, String outputPath,
			SecretKey aesKey) throws InvalidKeyException,
			NoSuchAlgorithmException, NoSuchPaddingException {

		Cipher aesCipher = Cipher.getInstance("AES/ECB/PKCS5Padding");
		aesCipher.init(Cipher.ENCRYPT_MODE, aesKey);

		FileInputStream is = null;
		CipherOutputStream os = null;

		try {
			is = new FileInputStream(new File(inputPath));
			os = new CipherOutputStream(new FileOutputStream(new File(outputPath)), aesCipher);
			streamCopy(is, os);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			closeQuietly(os);
			closeQuietly(is);
		}
	}

	// Step 4, Encrypts AES 256 key with public from receiver's certificate
	public static void encyrptWithPublicKey(String outputPath,
			String publicKeyFilePath, String keyStorePassword, String keyAlias,
			byte[] aesKey) throws GeneralSecurityException {

		CipherOutputStream os = null;

		try {
			// Get public Key from receiver's certificate
			KeyStore keyStore = KeyStore.getInstance("PKCS12");
			keyStore.load(new FileInputStream(publicKeyFilePath),
					keyStorePassword.toCharArray());
			Certificate cert = keyStore.getCertificate(keyAlias);
			PublicKey pulicKey = cert.getPublicKey();

			// write AES key
			Cipher pkCipher = Cipher.getInstance("RSA");
			pkCipher.init(Cipher.ENCRYPT_MODE, pulicKey);
			os = new CipherOutputStream(new FileOutputStream(new File(outputPath)), pkCipher);
			os.write(aesKey);
			os.flush();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			closeQuietly(os);
		}
	}

	// Step 2, Compress single file
	public static ZipOutputStream archive(String childfilePath,
			String parentFilePath, String outputPath) {

		ZipOutputStream zos = null;
		FileInputStream in = null;

		try {
			zos = new ZipOutputStream(new FileOutputStream(outputPath));
			zos.setLevel(Deflater.BEST_COMPRESSION);
			zos.setMethod(ZipOutputStream.DEFLATED);

			File parentNode = new File(parentFilePath);
			File node = new File(childfilePath);
			in = new FileInputStream(node);

			String fileCanonicalPath = node.getCanonicalPath().toString();
			String rootCanonicalPath = parentNode.getCanonicalPath().toString();
			String file = fileCanonicalPath.substring(rootCanonicalPath.length() + 1, fileCanonicalPath.length());

			// Create zip entry
			ZipEntry ze = new ZipEntry(file);
			zos.putNextEntry(ze);

			streamCopy(in, zos);

			zos.closeEntry();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			closeQuietly(zos);
			closeQuietly(in);
		}

		return zos;
	}

	// Step 5, Recursively compress multiple files stored in a ArrayList
	public static ZipOutputStream archive(List<String> fileList,
			String parentFilePath, String outputPath) {

		ZipOutputStream zos = null;

		try {
			zos = new ZipOutputStream(new FileOutputStream(outputPath));
			zos.setLevel(Deflater.BEST_SPEED);
			zos.setMethod(ZipOutputStream.DEFLATED);

			System.out.println("Output to Zip : " + outputPath);

			for (String file : fileList) {

				// Create zip entry based on string stored in ArrayList
				System.out.println("File Added : " + file);
				ZipEntry ze = new ZipEntry(file);
				zos.putNextEntry(ze);

				// Read in files with full path
				File parentNode = new File(parentFilePath);
				FileInputStream in = null;
				try {
					in = new FileInputStream(parentNode + File.separator + file);
					streamCopy(in, zos);
				} catch (IOException e) {
					e.printStackTrace();
				} finally {
					closeQuietly(in);
				}
			}

			zos.closeEntry();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			closeQuietly(zos);
		}

		return zos;
	}

	// Traverse a directory and get all files, add them into fileList
	public static List<String> generateFileList(String childfilePath,
			String parentFilePath, List<String> filepPathList)
			throws IOException {

		File node = new File(childfilePath);
		File parentNode = new File(parentFilePath);
		// Add file in ArrayList if node is a file
		if (node.isFile()) {
			String fileCanonicalPath = node.getCanonicalPath().toString(); // Canonical path of current file
			String parentCanonicalPath = parentNode.getCanonicalPath().toString(); // Canonical path of parent directory

			// Get file name only and add into ArrayList, which will be used to create ZipEntry
			filepPathList.add(fileCanonicalPath.substring(
					parentCanonicalPath.length() + 1,
					fileCanonicalPath.length()));

		}

		// Recursive progress if node is a dir
		if (node.isDirectory()) {
			String[] subNode = node.list();

			for (String filename : subNode) {

				// Create full file path to be treated as file type
				String childFilePath = childfilePath + File.separator + filename;
				generateFileList(childFilePath, parentFilePath, filepPathList);
			}
		}

		return filepPathList;

	}

	public static Map<String, String> unarchive(String inputPath, String outputPath) {

		ZipInputStream zis = null;
		Map<String, String> unarchivedFiles = new HashMap<String, String>();
		
		// create output directory is not exists
		File directory = new File(outputPath);
		if (!directory.exists()) {
			directory.mkdir();
		}

		try {
			// get the zip file content
			zis = new ZipInputStream(new FileInputStream(inputPath));
			// get the zipped file list entry
			ZipEntry ze = zis.getNextEntry();

			while (ze != null) {

				String entryName = ze.getName();
				
				// put different entries in hashmap
				if (entryName.contains("_Payload.xml")) {
					unarchivedFiles.put("xml",
							outputPath + File.separator + entryName);

				} else if (entryName.contains("_Payload")) {
					unarchivedFiles.put("payload", 
							outputPath + File.separator + entryName);
				}

				if (entryName.contains("_Key")) {
					unarchivedFiles.put("key", 
							outputPath + File.separator + entryName);
				}
				
				File newfile = new File(outputPath + File.separator + entryName);

				System.out.println("File Unzip : " + newfile.getAbsoluteFile());

				// create the directories of the zip directory
				if (ze.isDirectory()) {

					File newDir = new File(newfile.getAbsolutePath());
					if (!newDir.exists()) {
						boolean success = newDir.mkdirs();
						if (success == false) {
							System.out.println("Problem creating Folder");
						}
					}
				} else {

					FileOutputStream fos = null;
					try {
						fos = new FileOutputStream(newfile);
						streamCopy(zis, fos);
					} catch (IOException e) {
						e.printStackTrace();
					} finally {
						closeQuietly(fos);
					}
				}
				ze = zis.getNextEntry();
			}
			
			zis.closeEntry();
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			closeQuietly(zis);
		}
		
		return unarchivedFiles;
	}

	public static SecretKey decryptWithPrivateKey(String inputPath,
			String privateKeyFilePath, String keyStorePassword,
			String keyPassword, String keyAlias)
			throws GeneralSecurityException {

		CipherInputStream cis = null;
		ByteArrayOutputStream baos = null;
		SecretKey originalAESKey = null;

		try {
			// Get public Key from receiver's certificate
			KeyStore keyStore = KeyStore.getInstance("PKCS12");
			keyStore.load(new FileInputStream(privateKeyFilePath),
					keyStorePassword.toCharArray());
			PrivateKey privateKey = (PrivateKey) keyStore.getKey(keyAlias,
					keyPassword.toCharArray());

			// Write AES key
			Cipher pkCipher = Cipher.getInstance("RSA");
			pkCipher.init(Cipher.DECRYPT_MODE, privateKey);
			cis = new CipherInputStream(
					new FileInputStream(new File(inputPath)), pkCipher);
			baos = new ByteArrayOutputStream();

			streamCopy(cis, baos);
			byte[] decryptedAESKey = baos.toByteArray();
			originalAESKey = new SecretKeySpec(decryptedAESKey, "AES");

			if (originalAESKey != null) {
				System.out.println("AES key is: " + DatatypeConverter.printBase64Binary(originalAESKey.getEncoded()));
			}
			
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			closeQuietly(cis);
			closeQuietly(baos);

		}

		return originalAESKey;
	}

	public static void decryptWithAESKey(SecretKey aesKey, String inputPath,
			String outputPath) throws GeneralSecurityException {

		FileOutputStream fos = null;
		CipherInputStream cis = null;

		try {

			// Write AES key
			Cipher aesCipher = Cipher.getInstance("AES/ECB/PKCS5Padding");
			aesCipher.init(Cipher.DECRYPT_MODE, aesKey);

			cis = new CipherInputStream(
					new FileInputStream(new File(inputPath)), aesCipher);
			fos = new FileOutputStream(new File(outputPath));

			streamCopy(cis, fos);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			closeQuietly(cis);
			closeQuietly(fos);
		}
	}
	
	public static boolean validateXmlSignature(String inputPath) throws Exception {

		boolean coreValidity = false;
		
		XMLSignatureFactory fac = XMLSignatureFactory.getInstance("DOM");
		DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
		dbf.setNamespaceAware(true);
		Document doc = dbf.newDocumentBuilder().parse(
				new FileInputStream(inputPath));

		// Find Signature element.
		NodeList nl = doc.getElementsByTagNameNS(XMLSignature.XMLNS,
				"Signature");

		if (nl.getLength() == 0) {
			throw new Exception("Cannot find Signature element");
		}

		// Create a DOMValidateContext and specify a KeySelector
		// and document context.
		DOMValidateContext valContext = new DOMValidateContext(
				new X509KeySelector(), nl.item(0));

		// Unmarshal the XMLSignature.
		XMLSignature signature = fac.unmarshalXMLSignature(valContext);

		// Validate the XMLSignature.
		coreValidity = signature.validate(valContext);

		// Check core validation status.
		if (coreValidity == false) {
			System.err.println("Signature failed core validation");
			boolean sv = signature.getSignatureValue().validate(valContext);
			System.out.println("signature validation status: " + sv);
			if (sv == false) {
				// Check the validation status of each Reference.
				@SuppressWarnings("rawtypes")
				Iterator i = signature.getSignedInfo().getReferences()
						.iterator();
				for (int j = 0; i.hasNext(); j++) {
					boolean refValid = ((Reference) i.next())
							.validate(valContext);
					System.out.println("ref[" + j + "] validity status: "
							+ refValid);
				}
			}
		}

		return coreValidity;

	}

	// Copy a stream
	private static void streamCopy(InputStream is, OutputStream os)
			throws IOException {
		int i;
		byte[] b = new byte[BUFFER_SIZE];
		while ((i = is.read(b)) != -1) {
			os.write(b, 0, i);
		}
	}

	// Close a possibly null stream ignoring IOExceptions
	private static void closeQuietly(Closeable closeable) {
		if (closeable != null) {
			try {
				closeable.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
}

class X509KeySelector extends KeySelector {

	public KeySelectorResult select(KeyInfo keyInfo, Purpose purpose,
			AlgorithmMethod method, XMLCryptoContext context)
			throws KeySelectorException {

		Iterator ki = keyInfo.getContent().iterator();
		while (ki.hasNext()) {
			XMLStructure info = (XMLStructure) ki.next();
			if (!(info instanceof X509Data))
				continue;
			X509Data x509Data = (X509Data) info;

			Iterator xi = x509Data.getContent().iterator();
			while (xi.hasNext()) {
				Object o = xi.next();
				if (!(o instanceof X509Certificate))
					continue;
				final PublicKey key = ((X509Certificate) o).getPublicKey();

				// Make sure the algorithm is compatible
				// with the method.
				if (algEquals(method.getAlgorithm(), key.getAlgorithm())) {
					return new KeySelectorResult() {
						public Key getKey() {
							return key;
						}
					};
				}

			}

		}
		throw new KeySelectorException("No key found!");
	}

	private boolean algEquals(String algURI, String algName) {
		if ((algName.equalsIgnoreCase("DSA") && algURI
				.equalsIgnoreCase(SignatureMethod.DSA_SHA1))
				|| (algName.equalsIgnoreCase("RSA") && algURI
						.equalsIgnoreCase(SignatureMethod.RSA_SHA1))
				|| (algName.equalsIgnoreCase("RSA") && algURI
						.equalsIgnoreCase("http://www.w3.org/2001/04/xmldsig-more#rsa-sha256"))) {
			return true;
		} else {
			return false;
		}
	}

}
