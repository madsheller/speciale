library(tidyverse)
library(caret)
library(ROCR)
library(data.table)
library(fastglm)
library(ranger)
library(beepr)
library(mgcv)
library(lightgbm)
library(Rfast)
library(Matrix)


#### Data generating process ####

dgp <- function(N,
                dim, 
                nsim = 1,
                seed = NULL,
                beta = NULL,
                unobs = 0,
                noiseless = F){
  if(!is.null(seed)){
    set.seed(seed)
  }
  
  #### Settings ####
  if(dim == 0){
    stop("No covariates")
  }
  sim <- rep(1:nsim, each=N)
  
  if(unobs > 0){
    dim <- dim+unobs
  }
  
  ## EXOGENEOUS VARIABLES ##
  U_X <- sapply(1:dim, function(x) runif(N*nsim))
  U_T <- runif(N*nsim)
  q <- 0.5
  U_Y <- rbinom(N*nsim,1,q)
  
  # Remove noise on T and Y if noiseless 
  if(noiseless == T){
    U_T <- 0
    U_Y <- 0
  }

  ## FUNCTIONS ##
  # Coeffients
  beta_T <- runif(dim, -0.3, 0.3)
  beta_Y <- runif(dim, -0.3, 0.3)
  beta_tau <- runif(dim, -0.2, 0.2)
  alpha_tau <- runif(1,0,0.1)
  if(dim > 5){
    no_het <- sample(1:dim, floor(dim/4), replace = F)
    beta_tau[no_het] <- 0
  }
  
  f_X <- function(ux) {ux}
  f_T <- function(x,ut) {
    2*(dim+1)*x%*%beta_T+ut
    }
  f_Y <- function(x,t,uy) {
    c <- x%*%beta_Y + t*x%*%(beta_tau+alpha_tau) + (uy-q)/10
    #m <- alpha_tau/2+alpha_tau*sum(beta_T)/(4*(dim+1))+sum(beta_tau)/4
    n <- length(c)
    m <- sum(c)/n
    s <- sum((c-m)^2)/(n-1)
    1*(c < m+s/2)
  }
  
  ## ENDOGENEOUS VARIABLES AND COUNTERFACTUALS ##
  X <- f_X(U_X)
  W <- f_T(X, U_T)
  Y <- f_Y(X, W, U_Y)
  
  #if(unobs > 0){
  #  dim <- dim-unobs
  #  X <- X[,1:dim]
  #  beta_T <- beta_T[1:dim]
  #  beta_Y <- beta_Y[1:dim]
  #  beta_tau <- beta_tau[1:dim]
  #}
  
  ## DATA ##
  X.int <- apply(X, 2, function(x) x*W)
  obs <- cbind(1,X, W, X.int)  
  x.names <- sapply(1:dim, FUN = function(s) paste0("x", s))
  x.names.int <- sapply(1:dim, FUN = function(s) paste0("x", s,":t"))
  x.names.obs <- c(x.names[1:(dim-unobs)], x.names.int[1:(dim-unobs)])
  nam <- c('intercept', x.names, 't', x.names.int)
  colnames(obs) <- nam
  
  return(list(obs=obs, y=Y, U_Y=U_Y,
              x.names.obs = x.names.obs,
              beta = list(beta_tau=beta_tau,
                          beta_T=beta_T,
                          beta_Y=beta_Y,
                          alpha_tau=alpha_tau)))
}

#### MEASURES ####
ASAM <- function(preds, vars, t){
  K <- ncol(vars)
  treat_id <- which(t==1)
  comp_id <- which(t==0)
  N1 <- length(treat_id)
  
  mu <- 1 / N1 * apply(vars[treat_id,], 2, sum)
  w_mu <- t(preds[comp_id]) %*% vars[comp_id,] / sum(preds[comp_id])
  s <- sqrt(diag(t(vars[treat_id,] - mu) %*% (vars[treat_id,] - mu)) / (N1 - 1))
  ASAM <- 1 / K * sum(abs(mu-w_mu) / s)
  return(ASAM)
}

SMD <- function(x,t){
  t0 <- which(t==0)
  t1 <- which(t==1)
  n0 <- length(t0)
  n1 <- length(t1)
  
  mu0 <- sum(x[t0])/n0
  mu1 <- sum(x[t1])/n1
  s0 <- sum((x[t0]-mu0)^2)/(n0-1)
  s1 <- sum((x[t1]-mu1)^2)/(n1-1)
  
  SMD <- abs(mu0-mu1)/sqrt((s0+s1)/2)
  return(SMD)
}

#### Matching ####

ps <- function(data,
               t,
               ps.method="glm"){
  
  if(ps.method=="glm"){
    pi <- fastglm(data[,1:11], 1*t, family = binomial(), method = 2)$coef
    ps <- data[,1:11]%*%pi
  } else if(ps.method=="gbm"){
    train_params <- list(
      max_depth = 4L,
      learning_rate = 0.05,
      objective = "binary",
      subsample = 0.8
    )
    dtrain <- lgb.Dataset(data[,2:11], label=1*t)
    model <- lgb.train(data = dtrain,
                       nrounds=100L,
                       params = train_params,
                       verbose = -1)
    ps <- predict(model,data[,2:11])
    ps <- log(ps/(1-ps))
  }
  suppressWarnings(ASAM_before <- ASAM(rep(1,nrow(data)), data[,2:11], t))
  suppressWarnings(ASAM_after <- ASAM(exp(ps), data[,2:11], t))
  
  return(list(ps=ps, ASAM.before=ASAM_before, ASAM.after=ASAM_after))
}


matchfit <- function(pi,
                     t,
                     y,
                     data,
                     w_replace=T,
                     caliper = 0.1,
                     method = "ps"){
  ## setup
  sd_pi <- sd(pi)
  N <- length(pi)
  
  x <- data[,2:11]
  S <- diag(1, nrow=ncol(x))
  
  Match <- Matrix(0,nrow=N, ncol=2) #(y1,y0)
  Match_id <- Matrix(numeric(N*2),ncol=1)
  Nt <- which(t == 0)
  for(i in which(t==1)){
    psDist <- abs(pi[i]-pi[Nt])
    if(method=='ps'){
      closest <- which.min(psDist)
      if(psDist[closest] < 0.2*sd_pi){
        # Cross impute
        Match[i, 2] <- y[Nt[closest]]
        Match[Nt[closest], 1] <- y[i]
        # Remove from the pool.
        if(w_replace==T){
          pi[Nt[closest]] <- -Inf # -Inf such that ps-(-Inf)=Inf
        }
        # These rows have an imputation
        Match_id[i] <- 1
        Match_id[Nt[closest]] <- 1
      } 
    }
    else if(method=='hybrid'){
      ii <- which(psDist < 0.1*sd_pi)
      if(length(ii) == 0){
        Match[i, ] <- 0
      } else if(length(ii) == 1){
        Match[i, 2] <- y[Nt[ii]]
        Match[Nt[ii], 1] <- y[i]
        Match_id[i] <- 1
        Match_id[Nt[ii]] <- 1
        if(w_replace ==T ){
          pi[Nt[ii]] <- -Inf
        }
      } else{
        subclass <- t(x[Nt[ii],])
        dif <- apply(subclass, 2, function(z) t(x[i,]-z))
        Distance_maha <- apply(dif, 2, function(z) t(z)%*%S%*%z)
        closest <- which.min(Distance_maha)
        Match[i, 2] <- y[Nt[closest]]
        Match[Nt[closest], 1] <- y[i]
        Match_id[i] <- 1
        Match_id[Nt[closest]] <- 1
        if(w_replace ==T ){
          pi[Nt[ii]] <- -Inf
        }
      }
    }
  }
  prune <- which(Match_id==1)
  
  # Augmented response matrix
  Augm_Response <- matrix(NA,nrow=N, ncol=2)
  Z <- t(sapply(1:N, FUN = function(x) (t[x]==c(0,1))))
  # Observed response
  Augm_Response[which(Z == T, arr.ind = T)] <- y
  # Impute counterfactual
  Augm_Response[which(Z != T, arr.ind = T)][prune] <- as.vector(Match)[prune]
  Augm_Response <- c(Augm_Response)
  prune <- is.na(Augm_Response)
  
  data <- data[,1:11]
  Augm <- rbind(cbind(data,t=0), cbind(data,t=1))[!prune,]
  Augm <- cbind(Augm,
                "x1:t"=Augm[,2]*Augm[,'t'],
                "x2:t"=Augm[,3]*Augm[,'t'],
                "x3:t"=Augm[,4]*Augm[,'t'],
                "x4:t"=Augm[,5]*Augm[,'t'],
                "x5:t"=Augm[,6]*Augm[,'t'],
                "x6:t"=Augm[,7]*Augm[,'t'],
                "x7:t"=Augm[,8]*Augm[,'t'],
                "x8:t"=Augm[,9]*Augm[,'t'],
                "x9:t"=Augm[,10]*Augm[,'t'],
                "x10:t"=Augm[,11]*Augm[,'t'])
  return(list(matched_sample = Augm,
              prune=prune,
              y=c(Augm_Response)[!prune]))
}


#### Regression tool ####
regression <- function(data,
                       t,
                       y,
                       newdata,
                       U_Y,
                       beta,
                       X.obs,
                       rf.ntree = 500){
  
  ## Data
  N <- nrow(X.obs)
  ## Counterfactuals
  q <- 0.5
  dim <- 10
  f_Y <- function(x,t,uy) {
    c <- x%*%beta$beta_Y + t*x%*%(beta$beta_tau+beta$alpha_tau) + (uy-q)/10
    m <- beta$alpha_tau/2+beta$alpha_tau*sum(beta$beta_T)/(4*(dim+1))+
      sum(beta$beta_tau)/4
    1*(c < m)
  }
  W.cf <- quantile(t, c(0.25, 0.75))
  py0 <- f_Y(X.obs,W.cf[1],0)*(1-q)+f_Y(X.obs,W.cf[1],1)*q
  py1 <- f_Y(X.obs,W.cf[2],0)*(1-q)+f_Y(X.obs,W.cf[2],1)*q
  trATE <- sum(f_Y(X.obs,W.cf[2],U_Y)-f_Y(X.obs,W.cf[1],U_Y))/N
  rm( W.cf,q)
  
  t0_id <- which(newdata[,'t']==0)
  t1_id <- which(newdata[,'t']==1)
  
  #### LINEAR MODEL ####
  fit <- coef(.lm.fit(data, y))
  pred <- newdata%*%fit
  
  lm.rmse <- c(RMSE0=RMSE(pred[t0_id], py0),
               RMSE1=RMSE(pred[t1_id], py1),
               BIAS=sum(pred[t1_id]-pred[t0_id])/N-trATE)
  
  #### GLM ####
  fit <- coef(fastglm(data, y, family = binomial(), method = 2))
  pred <- 1/(1+exp(-newdata%*%fit))
  
  glm.rmse <- c(RMSE0=RMSE(pred[t0_id], py0),
                RMSE1=RMSE(pred[t1_id], py1),
                BIAS=sum(pred[t1_id]-pred[t0_id])/N-trATE)
  #### Random Forest ####
  train <- cbind(data[,2:11],t=data[,'t'], y=y)
  newdata[,12] <- newdata[,'t']
  colnames(newdata)[12] <- 't'
  
  fit <- ranger(dependent.variable.name = 'y',
                data = train, classification = T,
                probability = T, num.trees = rf.ntree)
  pred <- predict(fit, newdata[,2:12])$predictions[,2]
  
  rf.rmse <- c(RMSE0=RMSE(pred[t0_id], py0),
               RMSE1=RMSE(pred[t1_id], py1),
               BIAS=sum(pred[t1_id]-pred[t0_id])/N-trATE)
  
  #### GAM ####
  x.names <- sapply(1:10,function(i)paste0("x",i))
  s_form<-as.formula(
    paste0("y~",
           paste0("s(",x.names,")",collapse="+"),
           collapse="")
  )
  s_form <- update(s_form, .~.+t)
  fit <- gam(s_form, family = binomial(), data = as.data.table(train))
  pred <- c(predict(fit, newdata=as.data.table(newdata[,2:12]), type="response"))

  gam.rmse <- c(RMSE0=RMSE(pred[t0_id], py0),
                RMSE1=RMSE(pred[t1_id], py1),
                BIAS=sum(pred[t1_id]-pred[t0_id])/N-trATE)
    
  res <- rbind(lm = lm.rmse,
               glm = glm.rmse,
               gam = gam.rmse,
               rf = rf.rmse)
  
  return(res)
}


