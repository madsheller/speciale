library(tidyverse)
library(caret)
library(ROCR)
library(data.table)
library(fastglm)
library(ranger)
library(beepr)
library(mgcv)
library(lightgbm)


#### Data generating process ####

dgp <- function(N,
                dim_cont, 
                dim_cat,
                overlap=1,
                nsim = 1,
                seed = NULL,
                beta = NULL,
                noiseless = F,
                corr=F,
                x.var = 1){
  if(!is.null(seed)){
    set.seed(seed)
  }
  
  #### Settings ####
  dim <- dim_cont + dim_cat
  if(dim == 0){
    stop("No covariates")
  }
  sim <- rep(1:nsim, each=N)
  
  # Parameters for exogenous variables
  sig <- diag(1,dim)*x.var
  p <- 0.5
  q <- 0.5
  
  ## Generate correlations 
  if(corr == T){
    eig <- 0
    while(prod(eig)==0){
      A <- matrix(runif(2^dim)*2-1, dim)
      sigma <- t(A)%*%A
      diag(sigma) <- 1
      eig <- eigen(sigma)$values
    }
  }
  
  ## EXOGENEOUS VARIABLES ##
  U_X <- MASS::mvrnorm(N*nsim, rep(0,dim), sig)
  U_T <- rbinom(N*nsim, 1, p)
  U_Y <- rbinom(N*nsim, 1, q)
  
  # Create categorical covariates
  cat_levels <- 0
  if(dim_cat > 0){
    prob <- runif(1)
    size <- rbinom(dim_cat, size = 4, prob) + 2
    cat_levels <- sum(size)
    for(i in 1:dim_cat){
      breaks <- quantile(U_X[,i], probs = seq(0, 1, by=1/size[i]))
      U_X[,i] <- cut(U_X[,i], breaks = breaks, include.lowest=T, labels=F)
    }
    U_X <- as.data.table(U_X)
    U_X[, (1:dim_cat) := lapply(.SD, factor), .SDcols = 1:dim_cat]
  }
  
  # Remove noise on T and Y if noiseless 
  if(noiseless == T){
    U_T <- 0
    U_Y <- 0
  }
  
  beta_dim <- dim(U_X)[2]
  ## Function parameters 
  if(is.null(beta)){
    beta_T <- runif(beta_dim, -0.5, 0.5)
    beta_Y <- runif(beta_dim, -0.5, 0.5)
  } else {
    beta_T <- beta[[1]]
    beta_Y <- beta[[2]]
  }
  beta_tau <- runif(beta_dim, -0.5, 0.5)
  if(dim > 5){
    no_het <- sample(1:beta_dim, floor(beta_dim/4), replace = F)
    beta_tau[no_het] <- 0
  }
  
  ## Overlap assumption is satisfied for X's s.t. X*beta is in (th-1/d, th]
 # Q <- quantile(U_X%*%beta_T, 0.5)
  
  
  
  ## FUNCTIONS ##
  # Coeffients
  if(dim_cat>0){
    U_X <- model.matrix(~.-1,x)
  } 
  
  beta_dim <- dim(U_X)[2]
  beta_T <- runif(dim(U_X)[2], -3, 0.3)
  beta_Y <- runif(beta_dim, -0.3, 0.3)
  beta_tau <- runif(beta_dim, -0.2, 0.2)
  alpha_tau <- runif(1,0,0.1)
  if(dim > 5){
    no_het <- sample(1:beta_dim, floor(beta_dim/4), replace = F)
    beta_tau[no_het] <- 0
  }
  
  
  f_X <- function(ux) {ux}
  f_T <- function(x,ut) {
    #Q <- pmax(x%*%beta_T)
    c <- x%*%beta_T
    minc <- min(c)
    maxc <- max(c)
    tmax <- 1
    tmin <- -1
    x.std <- (c-minc)/(maxc-minc)*(tmax-tmin)+tmin
    #d <- sapply(c, function(y) (y-minc)/(maxc-minc))
    #sapply(p, function(y) rbinom(1,1,prob=y))
    #Q <- -0.5
    
    a <- overlap
    b <- 0
    (x.std > U_T - a)*(x.std < U_T + b) 
    }
  f_Y <- function(x,t,uy) {
    c <- x%*%beta_Y + t*x%*%(beta_tau+alpha_tau) + uy
    # Ensure non-degenerate Y
    v0 <- sum(beta_Y^2*x.var)
    v1 <- sum((beta_Y+beta_tau)^2*x.var)
    optQ <- function(b) {
      pnorm(b, 1+alpha_tau, v1)*p*q +
        pnorm(b, alpha_tau, v1)*p*(1-q) +
        pnorm(b, 1, v0)*(1-p)*q +
        pnorm(b, 0, v0)*(1-q)*(1-p) -
        0.7
    }
    d <- seq(-10,10, by=0.01)
    QY <- d[which.min(abs(sapply(d, FUN = optQ)))]
    #1*pmax((c>-1)*(c<1/2),(c>3/2)*(c<2))
    1*(c > QY)
  }
  
  ## ENDOGENEOUS VARIABLES AND COUNTERFACTUALS ##
  X <- f_X(U_X)
  W <- f_T(X, U_T)
  for(k in 1:nsim){
    if(sum(W[((k-1)*N+1):(k*N)])>N/2){W <- (W==F)}
  }
  Y0 <- f_Y(X, 0, U_Y)
  Y1 <- f_Y(X, 1, U_Y)
  Y <- Y0*(1-W) + Y1*W
  
  ## TRUE EXPECATION OF COUNTERFACTUALS ##
  y_temp0 <- f_Y(X, 0, 0)
  y_temp1 <- f_Y(X, 0, 1)
  y_0 <- y_temp0*(1-q) + y_temp1*q 
  
  y_temp0 <- f_Y(X, 1, 0)
  y_temp1 <- f_Y(X, 1, 1)
  y_1 <- y_temp0*(1-q) + y_temp1*q

  
  ## DATA ##
  obs <- cbind(sim, X, W, Y, Y0, Y1, y_0, y_1)
  obs <- as.data.table(obs)
  x.names <- sapply(1:dim, FUN = function(s) paste0("x", s))
  colnames(obs) <- c('sim', x.names,'t',
                     'y', 'y0', 'y1',
                     'py0', 'py1')
  
  # Convert to categorical
  if(dim_cat > 0){
    obs <- obs %>%
      mutate(across(.cols = num_range("x", 1:dim_cat), as.factor))
  }
  
  return(list(obs = obs,
              beta_mat = cbind(beta_T, beta_tau, beta_Y),
              dist_table = table(obs$t, obs$y),
              x.names = x.names))
}

#### MEASURES ####
ASAM <- function(preds, dtrain, names){
  vars <- dtrain[,..names] %>% as.matrix()
  T_i <- dtrain[,"t"]
  K <- ncol(vars)
  treat_id <- which(T_i==1)
  comp_id <- which(T_i==0)
  N1 <- length(treat_id)
  
  mu <- 1 / N1 * apply(vars[treat_id,], 2, sum)
  w_mu <- t(preds[comp_id]) %*% vars[comp_id] / sum(preds[comp_id])
  s <- sqrt(diag(t(vars[treat_id,] - mu) %*% (vars[treat_id,] - mu)) / (N1 - 1))
  ASAM <- 1 / K * sum(abs(mu-w_mu) / s)
  return(ASAM)
}

confusion <- function(pred,
                      label,
                      F1 = F){
  
  ## CONFUSION MATRIX ##
  
  ## Optimal threshold
  if(F1 == T){
    pred.obj <- prediction(predictions = pred, labels = label)
    perf <- performance(pred.obj, measure="prec", x.measure="rec")
    cutoffs <- data.frame(cut=perf@alpha.values[[1]], rec=perf@x.values[[1]],
                          prec=perf@y.values[[1]]) %>% 
      mutate(F1 = 2*prec*rec/(prec+rec))
    p <- cutoffs$cut[which.max(cutoffs$F1)]
  } else{
    pred.obj <- prediction(predictions = pred, labels = label)
    perf <- performance(pred.obj, measure="sens", x.measure="spec")
    cutoffs <- data.frame(cut=perf@alpha.values[[1]], spec=perf@x.values[[1]],
                          sens=perf@y.values[[1]]) %>% 
      mutate(score = sens+spec)
    p <- cutoffs$cut[which.max(cutoffs$score)]
  }
  
  ## Create confusion matrix
  confu <- table(Actual = label,
                 Predicted = pred > p)
  if(length(colnames(confu)) == 1){
    if(colnames(confu) == "FALSE"){
      confu <- cbind(c(0,0), confu)
      colnames(confu) <- c("TRUE", "FALSE")
    }
    else{
      confu <- cbind(confu, c(0,0))
      colnames(confu) <- c("TRUE", "FALSE")
    }
  }
  
  ## PERFORMANCE MEASURES ##
  rs <- rowSums(confu)
  sensiv <- confu[1,1]/rs[1]
  specif <- confu[2,2]/rs[2]
  bal_acc <- (specif+sensiv)/2
  
  perf <- c(bal_acc, specif, sensiv)
  
  return(perf)

}

#### Matching ####

ps <- function(data,
               x.names,
               ps.method="glm"){
  
  if(ps.method=="glm"){
    #X <- model.matrix(as.formula(paste("t", paste(x.names, collapse=" + "), sep=" ~ ")), data)
    X <- model.matrix(as.formula(paste("t", paste(x.names, collapse=" + "), sep=" ~ ")), data)
    pi <- fastglm(X, data$t, family = binomial(), method = 2)$coef
    ps <- X%*%pi
  } else if(ps.method=="gbm"){
    train_params <- list(
      max_depth = 4L,
      learning_rate = 0.05,
      objective = "binary",
      subsample = 0.8
    )
    train <- as.matrix(data[,..x.names])
    dtrain <- lgb.Dataset(train, label=c(data$t))
    model <- lgb.train(data = dtrain,
                       nrounds=100L,
                       params = train_params,
                       verbose = -1)
    ps <- predict(model,train)
    ps <- log(ps/(1-ps))
  }
  
  return(ps=ps)
}



matchfit <- function(data,
                     N,
                     ps.method,
                     w_replace=T,
                     caliper = 0.1,
                     method = "hybrid"){
  
  x.names <- names(data)[grepl("^x", names(data))]
  
  pi <- ps(data,x.names,ps.method=ps.method)
  sd_pi <- sd(pi)
  Bucket <- levels(factor(data$t))
  
  suppressWarnings(ASAM_before <- ASAM(rep(1,nrow(data)), data, x.names))
  suppressWarnings(ASAM_after <- ASAM(exp(pi), data, x.names))
  
  ### Missing counterfactual indicator
  Z <- t(sapply(1:N, FUN = function(x) (data$t[x]==Bucket)))

  # Covariance matrix
  #cont_cols <- c(setdiff(x.names,names(Filter(is.factor, data))),"t")
  #ps_form <- as.formula(paste("t", paste(cont_cols, collapse=" + "), sep=" ~ "))
  #mm <- model.matrix(update(ps_form, .~.-t-1), as.data.frame(data[,..cont_cols]))
  #cont_cols <- cont_cols[-which(cont_cols=="t")]
  #tryCatch(
  #  expr = {
  #    S <- solve(cov(mm))
  #  },
  #  error = function(e){
  #    method <- "ps"
  #  }
  #)
  S <- diag(1, nrow=length(x.names))
  

  Match <- matrix(nrow=N, ncol=2)
  c_id <- numeric(N*2)
  for(i in which(data$t==1)){
    Real <- (data$t[i]==Bucket)
    cFact <- Bucket[!Real]
    Nt <- which(data$t == cFact)
    psDist <- abs(pi[i]-pi[Nt])
    if(method=='ps'){
      closest <- which.min(psDist)
      if(psDist[closest] < 0.2*sd_pi){
        # Cross impute
        Match[i, 2] <- data$y[Nt[closest]]
        Match[Nt[closest], 1] <- data$y[i]
        # Remove from the pool.
        if(w_replace==T){
          pi[Nt[closest]] <- -Inf # -Inf such that ps-(-Inf)=Inf
        }
        # These rows have an imputation
        c_id[i] <- 1
        c_id[Nt[closest]] <- 1
      } 
    }
    else if(method=='hybrid'){
      ii <- which(psDist < 0.1*sd_pi)
      if(length(ii) == 0){
        Match[i, ] <- NA
      } else if(length(ii) == 1){
        Match[i, !Real] <- data$y[Nt[ii]]
        Match[Nt[ii], Real] <- data$y[i]
        c_id[i] <- i
        c_id[i+N] <- Nt[ii]
        if(w_replace ==T ){
          pi[Nt[ii]] <- -Inf
        }
      } else{
        subclass <- t(data[Nt[ii],..x.names])
        dif <- c(t(data[i,Nt[ii]]))-subclass
        Distance_maha <- apply(dif, 2, function(x) t(x)%*%S%*%x)
        closest <- which.min(Distance_maha)
        Match[i, !Real] <- data$y[Nt[closest]]
        Match[Nt[closest], Real] <- data$y[i]
        c_id[i] <- i
        c_id[i+N] <- Nt[closest]
        if(w_replace ==T ){
          pi[Nt[ii]] <- -Inf
        }
      }
    }
  }
  id <- apply(Match, 1, function(x) all(is.na(x)))
  
  # Augmented response
  Augm_Response <- matrix(nrow=N, ncol=2)
  # Observed response
  Augm_Response[which(Z == T, arr.ind = T)] <- data$y
  # Impute counterfactual
  Augm_Response[which(Z != T, arr.ind = T)][!id] <- Match[which(!is.na(Match[!id,]), arr.ind = T)]
  
  Augm <- rbind(data, data)
  Augm$t <- rep(c(0,1), each=N)
  Augm$y <- c(Augm_Response)
  Augm <- Augm[!is.na(y)]
  
  ## Evaluate performance of the imputations
  pred <- rowSums(Match[!id,], na.rm=T)
  lab <- (data$y0*data$t+(1-data$t)*data$y0)[!id]
  
  confu <- table(Actual = lab,
                 Predicted = pred)
  if(length(colnames(confu)) == 1){
    if(colnames(confu) == "FALSE"){
      confu <- cbind(c(0,0), confu)
      colnames(confu) <- c("TRUE", "FALSE")
    }
    else{
      confu <- cbind(confu, c(0,0))
      colnames(confu) <- c("TRUE", "FALSE")
    }
  }
  
  rs <- rowSums(confu)
  
  specif <- confu[1,1]/rs[1]
  sensiv <- confu[2,2]/rs[2]
  
  acc <- (specif+sensiv)/2
  
  perf <- c(acc, specif, sensiv)
  
  ## Evaluate performance of random guessing
  pred <- rbinom(length(pred), 1, prob = sum(data$y)/N)
  
  confu <- table(Actual = lab,
                 Predicted = pred)
  if(length(colnames(confu)) == 1){
    if(colnames(confu) == "FALSE"){
      confu <- cbind(c(0,0), confu)
      colnames(confu) <- c("TRUE", "FALSE")
    }
    else{
      confu <- cbind(confu, c(0,0))
      colnames(confu) <- c("TRUE", "FALSE")
    }
  }
  
  rs <- rowSums(confu)
  
  specif <- confu[1,1]/rs[1]
  sensiv <- confu[2,2]/rs[2]
  
  acc <- (specif+sensiv)/2
  
  perf_rand <- c(acc, specif, sensiv)
  
    
  return(list(matched_sample = list(Augm),
              n_matches = nrow(Augm)/2,
              ASAM = ASAM_before-ASAM_after,
              method = method,
              perf = list(perf),
              perf_rand = list(perf_rand)))
}


#### Regression tool ####
regression <- function(data, 
                       md,
                       rf.ntree = 500){
  
  x.names <- names(data)[grepl("^x", names(data))]
  ## Formulas
  form <- as.formula(paste("y", paste(x.names, collapse=" + "), sep=" ~ "))
  ps_form <- as.formula(paste("t", paste(x.names, collapse=" + "), sep=" ~ "))
  
  ## Data preperation
  full.train <- model.matrix(update(form, .~.*t), data)
  md.train <- model.matrix(update(form, .~.*t), md)
  y.md <- md$y
  t.obs <- data$t
  y.obs <- data$y
  t.cf <- 1*(t.obs == 0)
  y.cf <- data$y0*t.cf + (1-t.cf)*data$y1
  test.mm <- data[,..x.names]
  test.mm <- rbind(cbind(test.mm, t=t.cf), cbind(test.mm, t=t.obs))
  test <- model.matrix(update(form, .~.*t), cbind(test.mm, y=1))
  Offer <- (t.obs==test[,"t"] )
  test.md <- test[, which(colnames(test) %in% colnames(md.train))]
  
  y0 <- as.vector(data$py0)
  y1 <- as.vector(data$py1)
  trATE <- as.vector(mean(data$y1-data$y0))
  
  ## Check for missing categories in matched data
  sub <- F
  factor_names <- names(Filter(is.factor, data))
  sub_covariates <- x.names
  miss_id <- c()
  for (l in factor_names){
    var_test <- setdiff(levels(data[,..l]), levels(droplevels(md[,..l])))
    if(!identical(var_test, character(0))){
      miss_id <- rbind(miss_id, var_test)
      sub_covariates <- sub_covariates[-which(sub_covariates == l)]
    }
  }
  
  sub <- !(length(sub_covariates)==length(x.names))
  if(sub == T){
    m_id <- c()
    for(j in miss_id){
      id <- which(full.train[,j]==1)
      m_id <- rbind(m_id, id)
    }
  }
  
  ## Performance
  meas.nam <- c("RMSE0","RMSE1", "BIAS")
  perf <- matrix(numeric(2*3), ncol=2)
  rownames(perf) <- meas.nam
  colnames(perf) <- c("Unmatched", "Matched")
  
  #### LINEAR MODEL ####
  fit <- coef(.lm.fit(md.train, y.md))
  pred <- test.md%*%fit
  fit <- coef(.lm.fit(full.train, y.obs))
  pred.full <- test%*%fit
  if(sub==T){
    pred[m_id] <- pred.full[m_id]
  }
  
  perf[1,1] <- RMSE(pred[which(test[,"t"]==0)], y0) 
  perf[2,1] <- RMSE(pred[which(test[,"t"]==1)], y1)
  perf[1,2] <- RMSE(pred.full[which(test[,"t"]==0)], y0) 
  perf[2,2] <- RMSE(pred.full[which(test[,"t"]==1)], y1)
  perf[3,1] <- as.vector(mean(pred[which(test[,"t"]==1)]-pred[which(test[,"t"]==0)]))-trATE
  perf[3,2] <- as.vector(mean(pred.full[which(test[,"t"]==1)]-pred.full[which(test[,"t"]==0)]))-trATE
  
  lm <- perf
  
  #### GLM ####
  fit <- coef(fastglm(md.train, y.md, family = binomial(), method = 2))
  pred <- 1/(1+exp(-test.md%*%fit))
  fit <- coef(fastglm(full.train, y.obs, family = binomial(), method = 2))
  pred.full <- 1/(1+exp(-test%*%fit))
  if(sub==T){
    pred[m_id] <- pred.full[m_id]
  }
  
  perf[1,1] <- RMSE(pred[which(test[,"t"]==0)], y0) 
  perf[2,1] <- RMSE(pred[which(test[,"t"]==1)], y1)
  perf[1,2] <- RMSE(pred.full[which(test[,"t"]==0)], y0) 
  perf[2,2] <- RMSE(pred.full[which(test[,"t"]==1)], y1) 
  perf[3,1] <- as.vector(mean(pred[which(test[,"t"]==1)]-pred[which(test[,"t"]==0)]))-trATE
  perf[3,2] <- as.vector(mean(pred.full[which(test[,"t"]==1)]-pred.full[which(test[,"t"]==0)]))-trATE

  glm <- perf
  
  #### Random Forest ####
  df <- data[,..x.names]
  full_df <- list(cbind(df, t=0), cbind(df, t=1))
  counterfactual_df <- cbind(df, t=t.cf)
  
  fit <- ranger(dependent.variable.name = 'y',
                data = cbind(md[,..x.names], t=md$t, y=md$y),
                probability = T, num.trees = 700, classification = T)
  pred <- predict(fit, test.mm)$predictions[,2]
  perf[1,1] <- RMSE(pred[which(test[,"t"]==0)], y0) 
  perf[2,1] <- RMSE(pred[which(test[,"t"]==1)], y1)
  perf[3,1] <- as.vector(mean(pred[which(test[,"t"]==1)]-pred[which(test[,"t"]==0)]))-trATE
  
  fit <- ranger(dependent.variable.name = 'y',
                data = cbind(data[,..x.names], t=data$t, y=data$y),
                probability = T, num.trees = 700, classification = T)
  pred <- predict(fit, test.mm)$predictions[,2]
  perf[1,2] <- RMSE(pred[which(test[,"t"]==0)], y0) 
  perf[2,2] <- RMSE(pred[which(test[,"t"]==1)], y1)
  perf[3,2] <- as.vector(mean(pred[which(test[,"t"]==1)]-pred[which(test[,"t"]==0)]))-trATE
  
  rf <- perf
  
  #### GAM ####
  s_form<-as.formula(
    paste0("y~",
           paste0("s(",x.names,")",collapse="+"),
           collapse="")
  )
  s_form <- update(s_form, .~.+t)
  fit <- gam(s_form, family = binomial(), data = md)
  pred <- predict(fit, newdata=test.mm, type="response")
  fit <- gam(s_form, family = binomial(), data = data)
  pred.full <- predict(fit, newdata=test.mm, type="response")
  if(sub==T){
    pred[m_id] <- pred.full[m_id]
  }
  
  perf[1,1] <- RMSE(pred[which(test[,"t"]==0)], y0) 
  perf[2,1] <- RMSE(pred[which(test[,"t"]==1)], y1)
  perf[1,2] <- RMSE(pred.full[which(test[,"t"]==0)], y0) 
  perf[2,2] <- RMSE(pred.full[which(test[,"t"]==1)], y1) 
  perf[3,1] <- as.vector(mean(pred[which(test[,"t"]==1)]-pred[which(test[,"t"]==0)]))-trATE
  perf[3,2] <- as.vector(mean(pred.full[which(test[,"t"]==1)]-pred.full[which(test[,"t"]==0)]))-trATE
  
  gam <- perf
  
  return(list(lm = list(lm),
              gam = list(gam),
              glm = list(glm),
              rf = list(rf)))
}


#### Simulation ####

perfplot <- function(mod, title, measures = NULL){
  if(is.null(measures)){
    measures <- c("RMSE0","RMSE1", "BIAS")
  }
  p <- data.frame(typ= c("RMSE0","RMSE1", "BIAS"),
                  do.call(rbind, mod)) %>% 
    filter(typ == measures) %>% 
    pivot_longer(cols = c("Unmatched", "Matched")) %>% 
    ggplot(aes(x = value, color = factor(name))) +
    geom_histogram(fill="white", position = "identity", alpha=0.3) +
    facet_wrap(.~typ, scales = "free") +
    ggtitle(title)
  return(p)
}


sim <- function(N,
                nsim,
                dim_cont,
                dim_cat,
                overlap=1,
                seed=NULL,
                ps.method='glm',
                method = 'ps',
                caliper = 0.01,
                beta=NULL,
                unobs = 0,
                w_replace=T,
                noiseless = F){
  
    
  start <- Sys.time()
  df <- dgp(N = N, 
            nsim = nsim,
            dim_cont = dim_cont,
            dim_cat = dim_cat,
            beta = beta,
            overlap=overlap,
            noiseless = noiseless)
  
  if(unobs > 0){
    id <- paste0("x",sample(1:(dim_cont+dim_cat),unobs))
    df$obs[,-..id]
  }
  print(table(t=df$obs$t, y=df$obs$y)/(N*nsim))
  if(any((table(df$obs$t, df$obs$y) == 0))){
    print(table(t=df$obs$t, y=df$obs$y))
    stop("Degenerate")
  }
  
  
  # Prepare data
  d <- df$obs[,
              .(data=list(.SD)),
              by = sim]
  # Remove datasets that are too imbalanced
  ii <- d[,
          which(any(table(data[[1]]$t, data[[1]]$y)<N*0.01)),
          by = sim]$sim
  if(!identical(ii, numeric(0))){
    if(length(ii)==nsim){
      stop("Too much imbalance")
    }
    d <- d[-ii,]
  }
  # Match
  md <- d[,
          c("md", "n.matches", "ASAM", "method", "perf", "perf_rand") := matchfit(data[[1]],
                                                                                  N,
                                                                                  caliper,
                                                                                  w_replace=w_replace,
                                                                                  ps.method=ps.method,
                                                                                  method = method),
          by = sim]
  
  # Evaluate performance of the imputations alone
  imp <- do.call(rbind, md$perf) %>% 
    as.data.frame() %>% 
    `colnames<-`(c("Balanced accuracy", "Specificity", "Sensitivity")) 

  
  # Evaluate performance of the random guessing
  rand <- do.call(rbind, md$perf_rand) %>% 
    as.data.frame() %>% 
    `colnames<-`(c("Balanced accuracy", "Specificity", "Sensitivity"))  

  imp_perf <- cbind(typ=rep(c("imp","rand"), each=nrow(imp)),rbind(imp,rand), asam=md$ASAM) %>% 
    data.frame() %>% 
    `colnames<-`(c("typ","Balanced accuracy", "Specificity", "Sensitivity", "asam")) %>% 
    pivot_longer(cols=c("Balanced accuracy", "Specificity", "Sensitivity")) %>% 
    ggplot(aes(x=typ, y=value, group=typ)) +
    geom_point(aes(group=asam,fill = asam), alpha=.9,position= position_dodge(0.55),size=2, shape = 21)+
    geom_boxplot(color="black", fill="white", alpha=0, lwd=1) +
    scale_fill_gradient(low = "yellow", high = "red", na.value = NA) +
    facet_wrap(~name, scales="free") +
    theme_bw()+
    theme(legend.position="bottom")
      
  
  
  # Fit a model to the matched respectively unmatched data
  reg <- md[,
            c("lm", "glm", "gam", "rf") := regression(data[[1]], md[[1]]),
            by = sim]
  
  # Performance plots
  
  #plm <- perfplot(reg$lm, "LM")
  
  #pglm <- perfplot(reg$glm, "GLM")
  
  #prf <- perfplot(reg$rf, "RF")
  
  reg_perf <- rbind(
    data.frame(typ = c("RMSE0", "RMSE1", "BIAS"), mod="lm",
               do.call(rbind, reg$lm)) %>% 
      as.data.frame() %>% 
      pivot_longer(cols=c("Matched", "Unmatched")),
    data.frame(typ = c("RMSE0", "RMSE1", "BIAS"), mod="glm",
               do.call(rbind, reg$glm)) %>% 
      as.data.frame() %>% 
      pivot_longer(cols=c("Matched", "Unmatched")),
    data.frame(typ = c("RMSE0", "RMSE1", "BIAS"), mod="gam",
               do.call(rbind, reg$gam)) %>% 
      as.data.frame() %>% 
      pivot_longer(cols=c("Matched", "Unmatched")),
    data.frame(typ = c("RMSE0", "RMSE1", "BIAS"), mod="rf",
               do.call(rbind, reg$rf)) %>% 
      as.data.frame() %>% 
      pivot_longer(cols=c("Matched", "Unmatched"))
  ) %>% 
    ggplot(aes(x = mod, y=value, fill=factor(name)))+
    geom_boxplot() +
    facet_grid(typ~., scales = "free") +
    theme(legend.position="bottom") +
    theme_bw()
  
  end <- Sys.time()
  
  print(sprintf('it took %.2f %s', end-start, units(end-start)))
  
  beep()
  
  return(list(
    imp_perf = imp_perf,
    reg_perf= reg_perf,
    reg = reg,
    ASAM = md$ASAM,
    n_degs = length(ii)))
}
