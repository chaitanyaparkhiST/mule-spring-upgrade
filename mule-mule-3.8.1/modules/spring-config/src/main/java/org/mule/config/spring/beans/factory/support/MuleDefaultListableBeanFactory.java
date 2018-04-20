package org.mule.config.spring.beans.factory.support;

import java.io.IOException;
import java.io.NotSerializableException;
import java.io.ObjectInputStream;
import java.io.ObjectStreamException;
import java.io.Serializable;
import java.lang.annotation.Annotation;
import java.lang.ref.Reference;
import java.lang.reflect.Method;
import java.security.AccessController;
import java.security.PrivilegedAction;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import javax.inject.Provider;

import org.springframework.beans.BeansException;
import org.springframework.beans.FatalBeanException;
import org.springframework.beans.TypeConverter;
import org.springframework.beans.factory.BeanDefinitionStoreException;
import org.springframework.beans.factory.BeanFactory;
import org.springframework.beans.factory.BeanFactoryAware;
import org.springframework.beans.factory.CannotLoadBeanClassException;
import org.springframework.beans.factory.FactoryBean;
import org.springframework.beans.factory.NoSuchBeanDefinitionException;
import org.springframework.beans.factory.NoUniqueBeanDefinitionException;
import org.springframework.beans.factory.ObjectFactory;
import org.springframework.beans.factory.SmartFactoryBean;
import org.springframework.beans.factory.SmartInitializingSingleton;
import org.springframework.beans.factory.config.BeanDefinition;
import org.springframework.beans.factory.config.DependencyDescriptor;
import org.springframework.beans.factory.support.AbstractBeanDefinition;
import org.springframework.beans.factory.support.AutowireCandidateResolver;
import org.springframework.beans.factory.support.BeanDefinitionValidationException;
import org.springframework.beans.factory.support.DefaultListableBeanFactory;
import org.springframework.beans.factory.support.RootBeanDefinition;
import org.springframework.core.OrderComparator;
import org.springframework.lang.UsesJava8;
import org.springframework.util.Assert;
import org.springframework.util.ClassUtils;
import org.springframework.util.ObjectUtils;
import org.springframework.util.StringUtils;

import com.google.common.base.Optional;

@SuppressWarnings("serial")
public class MuleDefaultListableBeanFactory extends DefaultListableBeanFactory {

	private static Class<?> javaUtilOptionalClass = null;

	private static Class<?> javaxInjectProviderClass = null;

	static {
		try {
			javaUtilOptionalClass = ClassUtils.forName("java.util.Optional",
					DefaultListableBeanFactory.class.getClassLoader());
		} catch (ClassNotFoundException ex) {
			// Java 8 not available - Optional references simply not supported then.
		}
		try {
			javaxInjectProviderClass = ClassUtils.forName("javax.inject.Provider",
					DefaultListableBeanFactory.class.getClassLoader());
		} catch (ClassNotFoundException ex) {
			// JSR-330 API not available - Provider interface simply not supported then.
		}
	}

	/** Map from serialized id to factory instance */
	private static final Map<String, Reference<DefaultListableBeanFactory>> serializableFactories = new ConcurrentHashMap<String, Reference<DefaultListableBeanFactory>>(
			8);

	/** Optional id for this factory, for serialization purposes */
	private String serializationId;

	/** Map from dependency type to corresponding autowired value */
	private final Map<Class<?>, Object> resolvableDependencies = new HashMap<Class<?>, Object>(16);

	/** Map of bean definition objects, keyed by bean name */
	private final Map<String, BeanDefinition> beanDefinitionMap = new ConcurrentHashMap<String, BeanDefinition>(64);

	/** Map of singleton and non-singleton bean names, keyed by dependency type */
	private final Map<Class<?>, String[]> allBeanNamesByType = new ConcurrentHashMap<Class<?>, String[]>(64);

	/** Map of singleton-only bean names, keyed by dependency type */
	private final Map<Class<?>, String[]> singletonBeanNamesByType = new ConcurrentHashMap<Class<?>, String[]>(64);

	/** List of bean definition names, in registration order */
	private final List<String> beanDefinitionNames = new ArrayList<String>(64);

	/** List of names of manually registered singletons, in registration order */
	private final Set<String> manualSingletonNames = Collections.synchronizedSet(new LinkedHashSet<String>(16));

	/** Cached array of bean definition names in case of frozen configuration */
	private String[] frozenBeanDefinitionNames;

	/**
	 * Create a new DefaultListableBeanFactory.
	 */
	public MuleDefaultListableBeanFactory() {
		super();
	}

	/**
	 * Create a new DefaultListableBeanFactory with the given parent.
	 * 
	 * @param parentBeanFactory
	 *            the parent BeanFactory
	 */
	public MuleDefaultListableBeanFactory(BeanFactory parentBeanFactory) {
		super(parentBeanFactory);
	}

	/**
	 * Set a custom autowire candidate resolver for this BeanFactory to use when
	 * deciding whether a bean definition should be considered as a candidate for
	 * autowiring.
	 */
	public void setAutowireCandidateResolver(final AutowireCandidateResolver autowireCandidateResolver) {
		Assert.notNull(autowireCandidateResolver, "AutowireCandidateResolver must not be null");
		if (autowireCandidateResolver instanceof BeanFactoryAware) {
			if (System.getSecurityManager() != null) {
				final BeanFactory target = this;
				AccessController.doPrivileged(new PrivilegedAction<Object>() {
					@Override
					public Object run() {
						((BeanFactoryAware) autowireCandidateResolver).setBeanFactory(target);
						return null;
					}
				}, getAccessControlContext());
			} else {
				((BeanFactoryAware) autowireCandidateResolver).setBeanFactory(this);
			}
		}
	}

	@Override
	public <T> T getBean(Class<T> requiredType, Object... args) throws BeansException {
		Assert.notNull(requiredType, "Required type must not be null");
		String[] beanNames = getBeanNamesForType(requiredType);
		if (beanNames.length > 1) {
			ArrayList<String> autowireCandidates = new ArrayList<String>();
			for (String beanName : beanNames) {
				if (!containsBeanDefinition(beanName) || getBeanDefinition(beanName).isAutowireCandidate()) {
					autowireCandidates.add(beanName);
				}
			}
			if (autowireCandidates.size() > 0) {
				beanNames = autowireCandidates.toArray(new String[autowireCandidates.size()]);
			}
		}
		if (beanNames.length == 1) {
			return getBean(beanNames[0], requiredType, args);
		} else if (beanNames.length > 1) {
			Map<String, Object> candidates = new HashMap<String, Object>();
			for (String beanName : beanNames) {
				candidates.put(beanName, getBean(beanName, requiredType, args));
			}
			String primaryCandidate = determinePrimaryCandidate(candidates, requiredType);
			if (primaryCandidate != null) {
				return getBean(primaryCandidate, requiredType, args);
			}
			String priorityCandidate = determineHighestPriorityCandidate(candidates, requiredType);
			if (priorityCandidate != null) {
				return getBean(priorityCandidate, requiredType, args);
			}
			throw new NoUniqueBeanDefinitionException(requiredType, candidates.keySet());
		} else if (getParentBeanFactory() != null) {
			return getParentBeanFactory().getBean(requiredType, args);
		} else {
			throw new NoSuchBeanDefinitionException(requiredType);
		}
	}

	@Override
	public boolean containsBeanDefinition(String beanName) {
		Assert.notNull(beanName, "Bean name must not be null");
		return this.beanDefinitionMap.containsKey(beanName);
	}

	@Override
	public String[] getBeanDefinitionNames() {
		if (this.frozenBeanDefinitionNames != null) {
			return this.frozenBeanDefinitionNames;
		} else {
			return StringUtils.toStringArray(this.beanDefinitionNames);
		}
	}

	@Override
	public String[] getBeanNamesForType(Class<?> type, boolean includeNonSingletons, boolean allowEagerInit) {
		if (!isConfigurationFrozen() || type == null || !allowEagerInit) {
			return doGetBeanNamesForType(type, includeNonSingletons, allowEagerInit);
		}
		Map<Class<?>, String[]> cache = (includeNonSingletons ? this.allBeanNamesByType
				: this.singletonBeanNamesByType);
		String[] resolvedBeanNames = cache.get(type);
		if (resolvedBeanNames != null) {
			return resolvedBeanNames;
		}
		resolvedBeanNames = doGetBeanNamesForType(type, includeNonSingletons, allowEagerInit);
		if (ClassUtils.isCacheSafe(type, getBeanClassLoader())) {
			cache.put(type, resolvedBeanNames);
		}
		return resolvedBeanNames;
	}

	private String[] doGetBeanNamesForType(Class<?> type, boolean includeNonSingletons, boolean allowEagerInit) {
		List<String> result = new ArrayList<String>();

		// Check all bean definitions.
		for (String beanName : this.beanDefinitionNames) {
			// Only consider bean as eligible if the bean name
			// is not defined as alias for some other bean.
			if (!isAlias(beanName)) {
				try {
					RootBeanDefinition mbd = getMergedLocalBeanDefinition(beanName);
					// Only check bean definition if it is complete.
					if (!mbd.isAbstract() && (allowEagerInit
							|| ((mbd.hasBeanClass() || !mbd.isLazyInit() || isAllowEagerClassLoading()))
									&& !requiresEagerInitForType(mbd.getFactoryBeanName()))) {
						// In case of FactoryBean, match object created by FactoryBean.
						boolean isFactoryBean = isFactoryBean(beanName, mbd);
						boolean matchFound = (allowEagerInit || !isFactoryBean || containsSingleton(beanName))
								&& (includeNonSingletons || isSingleton(beanName)) && isTypeMatch(beanName, type);
						if (!matchFound && isFactoryBean) {
							// In case of FactoryBean, try to match FactoryBean instance itself next.
							beanName = FACTORY_BEAN_PREFIX + beanName;
							matchFound = (includeNonSingletons || mbd.isSingleton()) && isTypeMatch(beanName, type);
						}
						if (matchFound) {
							result.add(beanName);
						}
					}
				} catch (CannotLoadBeanClassException ex) {
					if (allowEagerInit) {
						throw ex;
					}
					// Probably contains a placeholder: let's ignore it for type matching purposes.
					if (this.logger.isDebugEnabled()) {
						this.logger.debug("Ignoring bean class loading failure for bean '" + beanName + "'", ex);
					}
					onSuppressedException(ex);
				} catch (BeanDefinitionStoreException ex) {
					if (allowEagerInit) {
						throw ex;
					}
					// Probably contains a placeholder: let's ignore it for type matching purposes.
					if (this.logger.isDebugEnabled()) {
						this.logger.debug("Ignoring unresolvable metadata in bean definition '" + beanName + "'", ex);
					}
					onSuppressedException(ex);
				}
			}
		}

		synchronized (manualSingletonNames) {
			// Check manually registered singletons too.
			for (String beanName : this.manualSingletonNames) {
				try {
					// In case of FactoryBean, match object created by FactoryBean.
					if (isFactoryBean(beanName)) {
						if ((includeNonSingletons || isSingleton(beanName)) && isTypeMatch(beanName, type)) {
							result.add(beanName);
							// Match found for this bean: do not match FactoryBean itself anymore.
							continue;
						}
						// In case of FactoryBean, try to match FactoryBean itself next.
						beanName = FACTORY_BEAN_PREFIX + beanName;
					}
					// Match raw bean instance (might be raw FactoryBean).
					if (isTypeMatch(beanName, type)) {
						result.add(beanName);
					}
				} catch (NoSuchBeanDefinitionException ex) {
					// Shouldn't happen - probably a result of circular reference resolution...
					if (logger.isDebugEnabled()) {
						logger.debug("Failed to check manually registered singleton with name '" + beanName + "'", ex);
					}
				}
			}
		}

		return StringUtils.toStringArray(result);
	}

	/**
	 * Check whether the specified bean would need to be eagerly initialized in
	 * order to determine its type.
	 * 
	 * @param factoryBeanName
	 *            a factory-bean reference that the bean definition defines a
	 *            factory method for
	 * @return whether eager initialization is necessary
	 */
	private boolean requiresEagerInitForType(String factoryBeanName) {
		return (factoryBeanName != null && isFactoryBean(factoryBeanName) && !containsSingleton(factoryBeanName));
	}

	@Override
	public String[] getBeanNamesForAnnotation(Class<? extends Annotation> annotationType) {
		List<String> results = new ArrayList<String>();
		for (String beanName : this.beanDefinitionNames) {
			BeanDefinition beanDefinition = getBeanDefinition(beanName);
			if (!beanDefinition.isAbstract() && findAnnotationOnBean(beanName, annotationType) != null) {
				results.add(beanName);
			}
		}

		synchronized (manualSingletonNames) {
			for (String beanName : this.manualSingletonNames) {
				if (!results.contains(beanName) && findAnnotationOnBean(beanName, annotationType) != null) {
					results.add(beanName);
				}
			}
		}

		return results.toArray(new String[results.size()]);
	}

	// ---------------------------------------------------------------------
	// Implementation of ConfigurableListableBeanFactory interface
	// ---------------------------------------------------------------------

	@Override
	public void registerResolvableDependency(Class<?> dependencyType, Object autowiredValue) {
		Assert.notNull(dependencyType, "Type must not be null");
		if (autowiredValue != null) {
			Assert.isTrue((autowiredValue instanceof ObjectFactory || dependencyType.isInstance(autowiredValue)),
					"Value [" + autowiredValue + "] does not implement specified type [" + dependencyType.getName()
							+ "]");
			this.resolvableDependencies.put(dependencyType, autowiredValue);
		}
	}

	@Override
	public BeanDefinition getBeanDefinition(String beanName) throws NoSuchBeanDefinitionException {
		BeanDefinition bd = this.beanDefinitionMap.get(beanName);
		if (bd == null) {
			if (this.logger.isTraceEnabled()) {
				this.logger.trace("No bean named '" + beanName + "' found in " + this);
			}
			throw new NoSuchBeanDefinitionException(beanName);
		}
		return bd;
	}

	@Override
	public void preInstantiateSingletons() throws BeansException {
		if (this.logger.isDebugEnabled()) {
			this.logger.debug("Pre-instantiating singletons in " + this);
		}

		// Iterate over a copy to allow for init methods which in turn register new bean
		// definitions.
		// While this may not be part of the regular factory bootstrap, it does
		// otherwise work fine.
		List<String> beanNames = new ArrayList<String>(this.beanDefinitionNames);

		// Trigger initialization of all non-lazy singleton beans...
		for (String beanName : beanNames) {
			RootBeanDefinition bd = getMergedLocalBeanDefinition(beanName);
			if (!bd.isAbstract() && bd.isSingleton() && !bd.isLazyInit()) {
				if (isFactoryBean(beanName)) {
					final FactoryBean<?> factory = (FactoryBean<?>) getBean(FACTORY_BEAN_PREFIX + beanName);
					boolean isEagerInit;
					if (System.getSecurityManager() != null && factory instanceof SmartFactoryBean) {
						isEagerInit = AccessController.doPrivileged(new PrivilegedAction<Boolean>() {
							@Override
							public Boolean run() {
								return ((SmartFactoryBean<?>) factory).isEagerInit();
							}
						}, getAccessControlContext());
					} else {
						isEagerInit = (factory instanceof SmartFactoryBean
								&& ((SmartFactoryBean<?>) factory).isEagerInit());
					}
					if (isEagerInit) {
						getBean(beanName);
					}
				} else {
					getBean(beanName);
				}
			}
		}

		// Trigger post-initialization callback for all applicable beans...
		for (String beanName : beanNames) {
			Object singletonInstance = getSingleton(beanName);
			if (singletonInstance instanceof SmartInitializingSingleton) {
				final SmartInitializingSingleton smartSingleton = (SmartInitializingSingleton) singletonInstance;
				if (System.getSecurityManager() != null) {
					AccessController.doPrivileged(new PrivilegedAction<Object>() {
						@Override
						public Object run() {
							smartSingleton.afterSingletonsInstantiated();
							return null;
						}
					}, getAccessControlContext());
				} else {
					smartSingleton.afterSingletonsInstantiated();
				}
			}
		}
	}

	// ---------------------------------------------------------------------
	// Implementation of BeanDefinitionRegistry interface
	// ---------------------------------------------------------------------

	@Override
	public void registerBeanDefinition(String beanName, BeanDefinition beanDefinition)
			throws BeanDefinitionStoreException {

		Assert.hasText(beanName, "Bean name must not be empty");
		Assert.notNull(beanDefinition, "BeanDefinition must not be null");

		if (beanDefinition instanceof AbstractBeanDefinition) {
			try {
				((AbstractBeanDefinition) beanDefinition).validate();
			} catch (BeanDefinitionValidationException ex) {
				throw new BeanDefinitionStoreException(beanDefinition.getResourceDescription(), beanName,
						"Validation of bean definition failed", ex);
			}
		}

		BeanDefinition oldBeanDefinition;

		oldBeanDefinition = this.beanDefinitionMap.get(beanName);
		if (oldBeanDefinition != null) {
			if (!isAllowBeanDefinitionOverriding()) {
				throw new BeanDefinitionStoreException(beanDefinition.getResourceDescription(), beanName,
						"Cannot register bean definition [" + beanDefinition + "] for bean '" + beanName
								+ "': There is already [" + oldBeanDefinition + "] bound.");
			} else if (oldBeanDefinition.getRole() < beanDefinition.getRole()) {
				// e.g. was ROLE_APPLICATION, now overriding with ROLE_SUPPORT or
				// ROLE_INFRASTRUCTURE
				if (this.logger.isWarnEnabled()) {
					this.logger.warn("Overriding user-defined bean definition for bean '" + beanName
							+ "' with a framework-generated bean definition: replacing [" + oldBeanDefinition
							+ "] with [" + beanDefinition + "]");
				}
			} else {
				if (this.logger.isInfoEnabled()) {
					this.logger.info("Overriding bean definition for bean '" + beanName + "': replacing ["
							+ oldBeanDefinition + "] with [" + beanDefinition + "]");
				}
			}
		} else {
			this.beanDefinitionNames.add(beanName);
			this.manualSingletonNames.remove(beanName);
			this.frozenBeanDefinitionNames = null;
		}
		this.beanDefinitionMap.put(beanName, beanDefinition);

		if (oldBeanDefinition != null || containsSingleton(beanName)) {
			resetBeanDefinition(beanName);
		}
	}

	@Override
	public void removeBeanDefinition(String beanName) throws NoSuchBeanDefinitionException {
		Assert.hasText(beanName, "'beanName' must not be empty");

		BeanDefinition bd = this.beanDefinitionMap.remove(beanName);
		if (bd == null) {
			if (this.logger.isTraceEnabled()) {
				this.logger.trace("No bean named '" + beanName + "' found in " + this);
			}
			throw new NoSuchBeanDefinitionException(beanName);
		}
		this.beanDefinitionNames.remove(beanName);
		this.frozenBeanDefinitionNames = null;

		resetBeanDefinition(beanName);
	}
	
	@Override
	public void registerSingleton(String beanName, Object singletonObject) throws IllegalStateException {
		super.registerSingleton(beanName, singletonObject);
		if (!this.beanDefinitionMap.containsKey(beanName)) {
			this.manualSingletonNames.add(beanName);
		}
		clearByTypeCache();
	}

	/**
	 * Remove any assumptions about by-type mappings.
	 */
	private void clearByTypeCache() {
		this.allBeanNamesByType.clear();
		this.singletonBeanNamesByType.clear();
	}

	// ---------------------------------------------------------------------
	// Dependency resolution functionality
	// ---------------------------------------------------------------------

	@Override
	public Object resolveDependency(DependencyDescriptor descriptor, String beanName, Set<String> autowiredBeanNames,
			TypeConverter typeConverter) throws BeansException {

		descriptor.initParameterNameDiscovery(getParameterNameDiscoverer());
		if (descriptor.getDependencyType().equals(javaUtilOptionalClass)) {
			return new OptionalDependencyFactory().createOptionalDependency(descriptor, beanName);
		} else if (descriptor.getDependencyType().equals(ObjectFactory.class)) {
			return new DependencyObjectFactory(descriptor, beanName);
		} else if (descriptor.getDependencyType().equals(javaxInjectProviderClass)) {
			return new DependencyProviderFactory().createDependencyProvider(descriptor, beanName);
		} else {
			Object result = getAutowireCandidateResolver().getLazyResolutionProxyIfNecessary(descriptor, beanName);
			if (result == null) {
				result = doResolveDependency(descriptor, beanName, autowiredBeanNames, typeConverter);
			}
			return result;
		}
	}

	public Object doResolveDependency(DependencyDescriptor descriptor, String beanName, Set<String> autowiredBeanNames,
			TypeConverter typeConverter) throws BeansException {

		Class<?> type = descriptor.getDependencyType();
		Object value = getAutowireCandidateResolver().getSuggestedValue(descriptor);
		if (value != null) {
			if (value instanceof String) {
				String strVal = resolveEmbeddedValue((String) value);
				BeanDefinition bd = (beanName != null && containsBean(beanName) ? getMergedBeanDefinition(beanName)
						: null);
				value = evaluateBeanDefinitionString(strVal, bd);
			}
			TypeConverter converter = (typeConverter != null ? typeConverter : getTypeConverter());
			return (descriptor.getField() != null ? converter.convertIfNecessary(value, type, descriptor.getField())
					: converter.convertIfNecessary(value, type, descriptor.getMethodParameter()));
		}

		if (type.isArray()) {
			Class<?> componentType = type.getComponentType();
			DependencyDescriptor targetDesc = new DependencyDescriptor(descriptor);
			targetDesc.increaseNestingLevel();
			Map<String, Object> matchingBeans = findAutowireCandidates(beanName, componentType, targetDesc);
			if (matchingBeans.isEmpty()) {
				if (descriptor.isRequired()) {
					raiseNoSuchBeanDefinitionException(componentType, "array of " + componentType.getName(),
							descriptor);
				}
				return null;
			}
			if (autowiredBeanNames != null) {
				autowiredBeanNames.addAll(matchingBeans.keySet());
			}
			TypeConverter converter = (typeConverter != null ? typeConverter : getTypeConverter());
			Object result = converter.convertIfNecessary(matchingBeans.values(), type);
			if (getDependencyComparator() != null && result instanceof Object[]) {
				Arrays.sort((Object[]) result, adaptDependencyComparator(matchingBeans));
			}
			return result;
		} else if (Collection.class.isAssignableFrom(type) && type.isInterface()) {
			Class<?> elementType = descriptor.getCollectionType();
			if (elementType == null) {
				if (descriptor.isRequired()) {
					throw new FatalBeanException("No element type declared for collection [" + type.getName() + "]");
				}
				return null;
			}
			DependencyDescriptor targetDesc = new DependencyDescriptor(descriptor);
			targetDesc.increaseNestingLevel();
			Map<String, Object> matchingBeans = findAutowireCandidates(beanName, elementType, targetDesc);
			if (matchingBeans.isEmpty()) {
				if (descriptor.isRequired()) {
					raiseNoSuchBeanDefinitionException(elementType, "collection of " + elementType.getName(),
							descriptor);
				}
				return null;
			}
			if (autowiredBeanNames != null) {
				autowiredBeanNames.addAll(matchingBeans.keySet());
			}
			TypeConverter converter = (typeConverter != null ? typeConverter : getTypeConverter());
			Object result = converter.convertIfNecessary(matchingBeans.values(), type);
			if (getDependencyComparator() != null && result instanceof List) {
				Collections.sort((List<?>) result, adaptDependencyComparator(matchingBeans));
			}
			return result;
		} else if (Map.class.isAssignableFrom(type) && type.isInterface()) {
			Class<?> keyType = descriptor.getMapKeyType();
			if (keyType == null || !String.class.isAssignableFrom(keyType)) {
				if (descriptor.isRequired()) {
					throw new FatalBeanException("Key type [" + keyType + "] of map [" + type.getName()
							+ "] must be assignable to [java.lang.String]");
				}
				return null;
			}
			Class<?> valueType = descriptor.getMapValueType();
			if (valueType == null) {
				if (descriptor.isRequired()) {
					throw new FatalBeanException("No value type declared for map [" + type.getName() + "]");
				}
				return null;
			}
			DependencyDescriptor targetDesc = new DependencyDescriptor(descriptor);
			targetDesc.increaseNestingLevel();
			Map<String, Object> matchingBeans = findAutowireCandidates(beanName, valueType, targetDesc);
			if (matchingBeans.isEmpty()) {
				if (descriptor.isRequired()) {
					raiseNoSuchBeanDefinitionException(valueType, "map with value type " + valueType.getName(),
							descriptor);
				}
				return null;
			}
			if (autowiredBeanNames != null) {
				autowiredBeanNames.addAll(matchingBeans.keySet());
			}
			return matchingBeans;
		} else {
			Map<String, Object> matchingBeans = findAutowireCandidates(beanName, type, descriptor);
			if (matchingBeans.isEmpty()) {
				if (descriptor.isRequired()) {
					raiseNoSuchBeanDefinitionException(type, "", descriptor);
				}
				return null;
			}
			if (matchingBeans.size() > 1) {
				String primaryBeanName = determineAutowireCandidate(matchingBeans, descriptor);
				if (primaryBeanName == null) {
					throw new NoUniqueBeanDefinitionException(type, matchingBeans.keySet());
				}
				if (autowiredBeanNames != null) {
					autowiredBeanNames.add(primaryBeanName);
				}
				return matchingBeans.get(primaryBeanName);
			}
			// We have exactly one match.
			Map.Entry<String, Object> entry = matchingBeans.entrySet().iterator().next();
			if (autowiredBeanNames != null) {
				autowiredBeanNames.add(entry.getKey());
			}
			return entry.getValue();
		}
	}

	private Comparator<Object> adaptDependencyComparator(Map<String, Object> matchingBeans) {
		Comparator<Object> comparator = getDependencyComparator();
		if (comparator instanceof OrderComparator) {
			return ((OrderComparator) comparator)
					.withSourceProvider(createFactoryAwareOrderSourceProvider(matchingBeans));
		} else {
			return comparator;
		}
	}

	private FactoryAwareOrderSourceProvider createFactoryAwareOrderSourceProvider(Map<String, Object> beans) {
		IdentityHashMap<Object, String> instancesToBeanNames = new IdentityHashMap<Object, String>();
		for (Map.Entry<String, Object> entry : beans.entrySet()) {
			instancesToBeanNames.put(entry.getValue(), entry.getKey());
		}
		return new FactoryAwareOrderSourceProvider(instancesToBeanNames);
	}

	/**
	 * Determine the autowire candidate in the given set of beans.
	 * <p>
	 * Looks for {@code @Primary} and {@code @Priority} (in that order).
	 * 
	 * @param candidateBeans
	 *            a Map of candidate names and candidate instances that match the
	 *            required type, as returned by {@link #findAutowireCandidates}
	 * @param descriptor
	 *            the target dependency to match against
	 * @return the name of the autowire candidate, or {@code null} if none found
	 */
	protected String determineAutowireCandidate(Map<String, Object> candidateBeans, DependencyDescriptor descriptor) {
		Class<?> requiredType = descriptor.getDependencyType();
		String primaryCandidate = determinePrimaryCandidate(candidateBeans, requiredType);
		if (primaryCandidate != null) {
			return primaryCandidate;
		}
		String priorityCandidate = determineHighestPriorityCandidate(candidateBeans, requiredType);
		if (priorityCandidate != null) {
			return priorityCandidate;
		}
		// Fallback
		for (Map.Entry<String, Object> entry : candidateBeans.entrySet()) {
			String candidateBeanName = entry.getKey();
			Object beanInstance = entry.getValue();
			if (this.resolvableDependencies.values().contains(beanInstance)
					|| matchesBeanName(candidateBeanName, descriptor.getDependencyName())) {
				return candidateBeanName;
			}
		}
		return null;
	}

	/**
	 * Raise a NoSuchBeanDefinitionException for an unresolvable dependency.
	 */
	private void raiseNoSuchBeanDefinitionException(Class<?> type, String dependencyDescription,
			DependencyDescriptor descriptor) throws NoSuchBeanDefinitionException {

		throw new NoSuchBeanDefinitionException(type, dependencyDescription,
				"expected at least 1 bean which qualifies as autowire candidate for this dependency. "
						+ "Dependency annotations: " + ObjectUtils.nullSafeToString(descriptor.getAnnotations()));
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder(ObjectUtils.identityToString(this));
		sb.append(": defining beans [");
		sb.append(StringUtils.collectionToCommaDelimitedString(this.beanDefinitionNames));
		sb.append("]; ");
		BeanFactory parent = getParentBeanFactory();
		if (parent == null) {
			sb.append("root of factory hierarchy");
		} else {
			sb.append("parent: ").append(ObjectUtils.identityToString(parent));
		}
		return sb.toString();
	}

	// ---------------------------------------------------------------------
	// Serialization support
	// ---------------------------------------------------------------------

	private void readObject(ObjectInputStream ois) throws IOException, ClassNotFoundException {
		throw new NotSerializableException("DefaultListableBeanFactory itself is not deserializable - "
				+ "just a SerializedBeanFactoryReference is");
	}

	protected Object writeReplace() throws ObjectStreamException {
		if (this.serializationId != null) {
			return new SerializedBeanFactoryReference(this.serializationId);
		} else {
			throw new NotSerializableException("DefaultListableBeanFactory has no serialization id");
		}
	}

	/**
	 * Minimal id reference to the factory. Resolved to the actual factory instance
	 * on deserialization.
	 */
	private static class SerializedBeanFactoryReference implements Serializable {

		private final String id;

		public SerializedBeanFactoryReference(String id) {
			this.id = id;
		}

		private Object readResolve() {
			Reference<?> ref = serializableFactories.get(this.id);
			if (ref == null) {
				throw new IllegalStateException(
						"Cannot deserialize BeanFactory with id " + this.id + ": no factory registered for this id");
			}
			Object result = ref.get();
			if (result == null) {
				throw new IllegalStateException(
						"Cannot deserialize BeanFactory with id " + this.id + ": factory has been garbage-collected");
			}
			return result;
		}
	}

	/**
	 * Separate inner class for avoiding a hard dependency on the
	 * {@code javax.inject} API.
	 */
	@UsesJava8
	private class OptionalDependencyFactory {

		public Object createOptionalDependency(DependencyDescriptor descriptor, String beanName) {
			DependencyDescriptor descriptorToUse = new DependencyDescriptor(descriptor) {
				@Override
				public boolean isRequired() {
					return false;
				}
			};
			descriptorToUse.increaseNestingLevel();
			return Optional.fromNullable(doResolveDependency(descriptorToUse, beanName, null, null));
		}
	}

	/**
	 * Serializable ObjectFactory for lazy resolution of a dependency.
	 */
	private class DependencyObjectFactory implements ObjectFactory<Object>, Serializable {

		private final DependencyDescriptor descriptor;

		private final boolean optional;

		private final String beanName;

		public DependencyObjectFactory(DependencyDescriptor descriptor, String beanName) {
			this.descriptor = new DependencyDescriptor(descriptor);
			this.descriptor.increaseNestingLevel();
			this.optional = this.descriptor.getDependencyType().equals(javaUtilOptionalClass);
			this.beanName = beanName;
		}

		@Override
		public Object getObject() throws BeansException {
			if (this.optional) {
				return new OptionalDependencyFactory().createOptionalDependency(this.descriptor, this.beanName);
			} else {
				return doResolveDependency(this.descriptor, this.beanName, null, null);
			}
		}
	}

	/**
	 * Serializable ObjectFactory for lazy resolution of a dependency.
	 */
	private class DependencyProvider extends DependencyObjectFactory implements Provider<Object> {

		public DependencyProvider(DependencyDescriptor descriptor, String beanName) {
			super(descriptor, beanName);
		}

		@Override
		public Object get() throws BeansException {
			return getObject();
		}
	}

	/**
	 * Separate inner class for avoiding a hard dependency on the
	 * {@code javax.inject} API.
	 */
	private class DependencyProviderFactory {

		public Object createDependencyProvider(DependencyDescriptor descriptor, String beanName) {
			return new DependencyProvider(descriptor, beanName);
		}
	}

	/**
	 * An {@link org.springframework.core.OrderComparator.OrderSourceProvider}
	 * implementation that is aware of the bean metadata of the instances to sort.
	 * <p>
	 * Lookup for the method factory of an instance to sort, if any, and let the
	 * comparator retrieve the {@link org.springframework.core.annotation.Order}
	 * value defined on it. This essentially allows for the following construct:
	 */
	private class FactoryAwareOrderSourceProvider implements OrderComparator.OrderSourceProvider {

		private final Map<Object, String> instancesToBeanNames;

		public FactoryAwareOrderSourceProvider(Map<Object, String> instancesToBeanNames) {
			this.instancesToBeanNames = instancesToBeanNames;
		}

		@Override
		public Object getOrderSource(Object obj) {
			return getFactoryMethod(this.instancesToBeanNames.get(obj));
		}

		private Method getFactoryMethod(String beanName) {
			if (beanName != null && containsBeanDefinition(beanName)) {
				BeanDefinition bd = getMergedBeanDefinition(beanName);
				if (bd instanceof RootBeanDefinition) {
					return ((RootBeanDefinition) bd).getResolvedFactoryMethod();
				}
			}
			return null;
		}
	}
}
